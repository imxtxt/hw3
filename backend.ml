(* ll ir compilation -------------------------------------------------------- *)

open Ll
open X86

(* Overview ----------------------------------------------------------------- *)

(* We suggest that you spend some time understinging this entire file and 
   how it fits with the compiler pipeline before making changes.  The suggested
   plan for implementing the compiler is provided on the project web page. 
*)


(* helpers ------------------------------------------------------------------ *)

(* Map LL comparison operations to X86 condition codes *)
let compile_cnd = function
  | Ll.Eq  -> X86.Eq
  | Ll.Ne  -> X86.Neq
  | Ll.Slt -> X86.Lt
  | Ll.Sle -> X86.Le
  | Ll.Sgt -> X86.Gt
  | Ll.Sge -> X86.Ge


(* Generate a function that can generate stack_offset *)
let stack_offset () =
  let i = ref 0L in
  fun () ->
     i := Int64.sub !i 8L;
    !i
  
(* Generate names for alloca *)    
let org_name = "a"
let alloca_name_ = ref (org_name ^ "0")

let alloca_name () = 
  let len = String.length !alloca_name_ in
  let num = String.sub !alloca_name_ 1 (len - 1) in
  let num = int_of_string num in
  let num = num + 1 in
  let num = string_of_int num in
  alloca_name_ := org_name ^ num;
  !alloca_name_

let clear_alloca () =
  alloca_name_ := org_name ^ "0"


let exit_lable (u) = u^"exit"
let cur_func = ref ""


let x86_op_by_ll_op (b: Ll.bop) =
  match b with
    | Add -> Addq
    | Sub -> Subq
    | Mul -> Imulq
    | Shl -> Shlq
    | Lshr -> Shrq
    | Ashr -> Sarq
    | And -> Andq
    | Or -> Orq
    | Xor -> Xorq

(* locals and layout -------------------------------------------------------- *)

(* One key problem in compiling the LLVM IR is how to map its local
   identifiers to X86 abstractions.  For the best performance, one
   would want to use an X86 register for each LLVM %uid.  However,
   since there are an unlimited number of %uids and only 16 registers,
   doing so effectively is quite difficult.  We will see later in the
   course how _register allocation_ algorithms can do a good job at
   this.

   A simpler, but less performant, implementation is to map each %uid
   in the LLVM source to a _stack slot_ (i.e. a region of memory in
   the stack).  Since LLVMlite, unlike real LLVM, permits %uid locals
   to store only 64-bit data, each stack slot is an 8-byte value.

   [ NOTE: For compiling LLVMlite, even i1 data values should be
   represented as a 8-byte quad. This greatly simplifies code
   generation. ]

   We call the datastructure that maps each %uid to its stack slot a
   'stack layout'.  A stack layout maps a uid to an X86 operand for
   accessing its contents.  For this compilation strategy, the operand
   is always an offset from ebp (in bytes) that represents a storage slot in
   the stack.  
*)

type layout = (uid * X86.operand) list

(* A context contains the global type declarations (needed for getelementptr
   calculations) and a stack layout. *)
type ctxt = { tdecls : (tid * ty) list
            ; layout : layout
            }

(* useful for looking up items in tdecls or layouts *)
let lookup m x = List.assoc x m


(* compiling operands  ------------------------------------------------------ *)

(* LLVM IR instructions support several kinds of operands.

   LL local %uids live in stack slots, whereas global ids live at
   global addresses that must be computed from a label.  Constants are
   immediately available, and the operand Null is the 64-bit 0 value.

     NOTE: two important facts about global identifiers:

     (1) You should use (Platform.mangle gid) to obtain a string 
     suitable for naming a global label on your platform (OS X expects
     "_main" while linux expects "main").

     (2) 64-bit assembly labels are not allowed as immediate operands.
     That is, the X86 code: movq _gid %rax which looks like it should
     put the address denoted by _gid into %rax is not allowed.
     Instead, you need to compute an %rip-relative address using the
     leaq instruction:   leaq _gid(%rip).

   One strategy for compiling instruction operands is to use a
   designated register (or registers) for holding the values being
   manipulated by the LLVM IR instruction. You might find it useful to
   implement the following helper function, whose job is to generate
   the X86 instruction that moves an LLVM operand into a designated
   destination (usually a register).  
*)
let compile_operand ctxt dest : Ll.operand -> ins =
function o ->
  begin match o with
    | Null ->
        (Movq, [Imm (Lit 0L); Reg dest])
    | Const c ->
        (Movq, [Imm (Lit c); Reg dest])
    | Gid g ->
        let g = Platform.mangle g in
        (Leaq, [Ind3 (Lbl g, Rip); Reg dest])
    | Id i ->
        let i = lookup ctxt.layout i in
        (Movq, [i; Reg dest])
  end



(* compiling call  ---------------------------------------------------------- *)

(* You will probably find it helpful to implement a helper function that 
   generates code for the LLVM IR call instruction.

   The code you generate should follow the x64 System V AMD64 ABI
   calling conventions, which places the first six 64-bit (or smaller)
   values in registers and pushes the rest onto the stack.  Note that,
   since all LLVM IR operands are 64-bit values, the first six
   operands will always be placed in registers.  (See the notes about
   compiling fdecl below.)

   [ NOTE: It is the caller's responsibility to clean up arguments
   pushed onto the stack, so you must free the stack space after the
   call returns. ]

   [ NOTE: Don't forget to preserve caller-save registers (only if
   needed). ]
*)



(* compiling getelementptr (gep)  ------------------------------------------- *)

(* The getelementptr instruction computes an address by indexing into
   a datastructure, following a path of offsets.  It computes the
   address based on the size of the data, which is dictated by the
   data's type.

   To compile getelmentptr, you must generate x86 code that performs
   the appropriate arithemetic calculations.
*)

(* [size_ty] maps an LLVMlite type to a size in bytes. 
    (needed for getelementptr)

   - the size of a struct is the sum of the sizes of each component
   - the size of an array of t's with n elements is n * the size of t
   - all pointers, I1, and I64 are 8 bytes
   - the size of a named type is the size of its definition

   - Void, i8, and functions have undefined sizes according to LLVMlite.
     Your function should simply return 0 in those cases
*)
let rec size_ty (tdecls: (tid * ty) list) (t: ty) : int =
  match t with
    | Void -> 0
    | I1 -> 8
    | I8 -> 0
    | I64 -> 8
    | Ptr _ -> 8
    | Struct ty_list -> 
        let t1 x = size_ty tdecls x in
        List.map (t1) ty_list |> List.fold_left (+) 0 
    | Array (len, ty) -> 
        let t1 = match ty with
                  | I8 -> 1
                  | _ -> (size_ty tdecls ty)
        in
        len * t1
    | Fun _ -> 0
    | Namedt n -> size_ty tdecls (List.assoc n tdecls)

(* Generates code that computes a pointer value.  

   1. op must be of pointer type: t*

   2. the value of op is the base address of the calculation

   3. the first index in the path is treated as the index into an array
     of elements of type t located at the base address

   4. subsequent indices are interpreted according to the type t:

     - if t is a struct, the index must be a constant n and it 
       picks out the n'th element of the struct. [ NOTE: the offset
       within the struct of the n'th element is determined by the 
       sizes of the types of the previous elements ]

     - if t is an array, the index can be any operand, and its
       value determines the offset within the array.
 
     - if t is any other type, the path is invalid

   5. if the index is valid, the remainder of the path is computed as
      in (4), but relative to the type f the sub-element picked out
      by the path so far
*)

(* 
  %struct.RT = type { i8, [10 x [20 x i32]], i8 }
  %struct.ST = type { i32, double, %struct.RT }

  define i32* @foo(%struct.ST* %s) nounwind uwtable readnone optsize ssp {
  entry:
    %arrayidx = getelementptr inbounds %struct.ST* %s, i64 1, i32 2, i32 1, i64 5, i64 13
    ret i32* %arrayidx
  }
*)

(* 
  Rax 
  Rax = Rax + 1 * len (struct.ST)
*)

let operand_const (o: Ll.operand): int =
  match o with
    | Const c -> Int64.to_int c
    | _ -> raise (Invalid_argument "t")

    
let rec real_type (tdecls : (tid * ty) list) (t: ty) = 
  match t with
    | Namedt n -> real_type tdecls (List.assoc n tdecls)
    | _ -> t

let compile_gep ctxt (op : Ll.ty * Ll.operand) (path: Ll.operand list) : ins list =
  let iii (t: Ll.ty * (ins list)) (o: Ll.operand) =
    let ty, ins = t in
    match ty with
    | Array (_, t) -> 
        let i1 = (compile_operand ctxt Rbx) o in
        let len = size_ty ctxt.tdecls t in
        let i2 = (Imulq, [Imm (Lit (Int64.of_int len)); Reg Rbx]) in
        let i3 = (Addq, [Reg Rbx; Reg Rax]) in
        let ttype = real_type ctxt.tdecls t in
        (ttype, ins @ [i1; i2; i3])

    | Struct ty_list ->
        let bias = operand_const o in
        let ttt = Array.of_list ty_list in
        let len = ref 0 in

        for i = 0 to bias - 1  do
          len := !len + size_ty ctxt.tdecls (Array.get ttt i)
        done;

        let i1 = (Addq, [Imm (Lit (Int64.of_int !len)); Reg Rax]) in
        let ttype = real_type ctxt.tdecls (Array.get ttt bias) in

        (ttype, ins @ [i1])

    | _ -> t
  in
    
  let t, o = op in

  let i =  (compile_operand ctxt Rax) o in

  let t = match t with
    | Ptr p -> Array (10, p)
    | _ -> raise (Invalid_argument "t")
  in

  let ttype = real_type ctxt.tdecls t in
  let t = List.fold_left (iii) (ttype, [i]) path in

  snd t

(* compiling instructions  -------------------------------------------------- *)

(* The result of compiling a single LLVM instruction might be many x86
   instructions.  We have not determined the structure of this code
   for you. Some of the instructions require only a couple assembly
   instructions, while others require more.  We have suggested that
   you need at least compile_operand, compile_call, and compile_gep
   helpers; you may introduce more as you see fit.

   Here are a few notes:

   - Icmp:  the Set instruction may be of use.  Depending on how you
     compile Cbr, you may want to ensure that the value produced by
     Icmp is exactly 0 or 1.

   - Load & Store: these need to dereference the pointers. Const and
     Null operands aren't valid pointers.  Don't forget to
     Platform.mangle the global identifier.

   - Alloca: needs to return a pointer into the stack

   - Bitcast: does nothing interesting at the assembly level
*)
let compile_insn ctxt (uid, i) : X86.ins list =
  begin match i with
    | Binop (bop, ty, src, dest) ->
        let i1 = (compile_operand ctxt Rbx) src in
        let i2 = (compile_operand ctxt Rcx) dest in
        let i3 = (x86_op_by_ll_op bop, [Reg Rcx; Reg Rbx]) in
        let i4 = (Movq, [Reg Rbx; lookup ctxt.layout uid]) in
        [i1; i2; i3; i4]

    | Icmp (cnd, ty, src, dest) ->
        let i1 = (compile_operand ctxt Rax) src in
        let i2 = (compile_operand ctxt Rbx) dest in
        let i3 = (Cmpq, [Reg Rbx; Reg Rax]) in
        let i4 = (Set (compile_cnd cnd), [Reg Rax]) in
        let i5  = (Movq, [Reg Rax; lookup ctxt.layout uid]) in
        [i1; i2; i3; i4; i5]

    | Load (ty, opd) ->
        let i1 = (compile_operand ctxt Rax) opd in
        let i2 = (Movq, [Ind2 Rax; Reg Rax]) in
        let i3 = (Movq, [Reg Rax; lookup ctxt.layout uid]) in
        [i1; i2; i3]

    | Store (ty, src, dest) ->
        let i1 = (compile_operand ctxt Rbx) src in
        let i2 = (compile_operand ctxt Rax) dest in
        let i3 = (Movq, [Reg Rbx; Ind2 Rax]) in
        [i1; i2; i3]

    | Alloca ty ->
        let a = alloca_name () in
        let i1 = (Leaq, [lookup ctxt.layout a; Reg Rax]) in
        let i2 = (Movq, [Reg Rax; lookup ctxt.layout uid]) in
        [i1; i2]

    | Call (ty, Gid name, param_list) ->
        let param_reg = [|Rdi; Rsi; Rdx; Rcx; R08; R09|] in

        let regg (i: int) (v: Ll.operand) =
          if i < 6 then
            [(compile_operand ctxt (Array.get param_reg i)) v]
          else
            let a = (compile_operand ctxt Rax) v in
            let b = (Pushq, [Reg Rax]) in
            [a; b]
        in
        let op_list = List.map snd param_list in
        let inss = List.mapi regg op_list |> List.flatten in
        let i1 = (Callq, [Imm (Lbl name)]) in
        let b = match ty with
          | Void -> inss @ [i1]
          | _ ->
            let t = (Movq, [Reg Rax; lookup ctxt.layout uid]) in
            inss @ [i1] @ [t]
        in
        let param_len = List.length param_list in
        if param_len > 6 then
          let var_on_stack = (param_len - 6) * 8 in
          b @ [(Addq, [Imm (Lit (Int64.of_int var_on_stack)); Reg Rsp])]
        else
          b
          
    | Bitcast (_, op, _) ->
        let i1 = (compile_operand ctxt Rax) op in
        let i2 = (Movq, [Reg Rax; lookup ctxt.layout uid]) in
        [i1; i2]

    | Gep (ty, operand, operands) ->
        let i1 =  compile_gep ctxt (ty, operand) operands in
        let i2 = (Movq, [Reg Rax; lookup ctxt.layout uid]) in
        i1 @ [i2]
      
    | _ -> []
  end



(* compiling terminators  --------------------------------------------------- *)

(* Compile block terminators is not too difficult:

   - Ret should properly exit the function: freeing stack space,
     restoring the value of %rbp, and putting the return value (if
     any) in %rax.

   - Br should jump

   - Cbr branch should treat its operand as a boolean conditional
*)
let compile_terminator ctxt t =
  match t with
    | Ret (Void, _) -> [(Jmp, [Imm (Lbl (exit_lable !cur_func))])]

    | Ret (t, o) -> 
        let o = match o with 
          | None -> raise Exit
          | Some a -> a
        in
        let b = o |> compile_operand ctxt Rax in
        [b; (Jmp, [Imm (Lbl (exit_lable !cur_func))])]

    | Br b -> [(Jmp, [Imm (Lbl b)])]

    | Cbr (op, t, e) -> 
        let b1 = op |> compile_operand ctxt Rax  in
        let b2 = (Cmpq, [Imm (Lit 1L); Reg Rax]) in
        let b3 = (J Neq, [Imm (Lbl e)]) in
        [b1; b2; b3]

(* compiling blocks --------------------------------------------------------- *)

(* We have left this helper function here for you to complete. *)
let compile_block ctxt blk : ins list =
  let comp_insn = compile_insn ctxt in
  let inss = List.map comp_insn blk.insns in
  let inss = List.flatten inss in
  inss @ compile_terminator ctxt (snd (blk.term))


let compile_lbl_block lbl ctxt blk : elem =
  Asm.text lbl (compile_block ctxt blk)



(* compile_fdecl ------------------------------------------------------------ *)


(* This helper function computes the location of the nth incoming
   function argument: either in a register or relative to %rbp,
   according to the calling conventions.  You might find it useful for
   compile_fdecl.

   [ NOTE: the first six arguments are numbered 0 .. 5 ]
*)
let arg_loc (n : int) : operand =
  let n = n + 1 in
  match n with
    | 1 -> Reg Rdi
    | 2 -> Reg Rsi
    | 3 -> Reg Rdx
    | 4 -> Reg Rcx
    | 5 -> Reg R08
    | 6 -> Reg R09
    | _ -> Ind3 (Lit (Int64.of_int (8 + 8 * (n - 6))) , Rbp)


(* We suggest that you create a helper function that computes the 
   stack layout for a given function declaration.

   - each function argument should be copied into a stack slot
   - in this (inefficient) compilation strategy, each local id 
     is also stored as a stack slot.
   - see the discusion about locals 

*)
let stack_layout args (block, lbled_blocks) : layout =
  let gen_off = stack_offset () in
  let gen_off_operand uid = (uid, Ind3 (Lit (gen_off ()), Rbp)) in
  let args_offs = List.map gen_off_operand args in
  let t2 acc i =
    let uid = fst i in
    let ins = snd i in
    match ins with
      | Store _  -> acc
      | Call (Void, _, _) -> acc
      | Alloca _ ->
          let x1 = [gen_off_operand (alloca_name ())] in
          let x2 = [gen_off_operand uid] in
          acc @ x1 @ x2
      | _ ->
          let t1 = [gen_off_operand uid] in
          acc @ t1
  in
  let t3 b = List.fold_left t2 [] b.insns in
  let blocks = block :: (List.map snd lbled_blocks) in
  let blocks_offs = List.map t3 blocks |> List.flatten in
  args_offs @ blocks_offs


(* The code for the entry-point of a function must do several things:

   - since our simple compiler maps local %uids to stack slots,
     compiling the control-flow-graph body of an fdecl requires us to
     compute the layout (see the discussion of locals and layout)

   - the function code should also comply with the calling
     conventions, typically by moving arguments out of the parameter
     registers (or stack slots) into local storage space.  For our
     simple compilation strategy, that local storage space should be
     in the stack. (So the function parameters can also be accounted
     for in the layout.)

   - the function entry code should allocate the stack storage needed
     to hold all of the local stack slots.
*)
let emit (i: ins list ref) (b: ins) = 
  i := !i @ [b]
  

let emits (i: ins list ref) (b: ins list) = 
  i := !i @ b

  
let compile_fdecl tdecls name { f_ty; f_param; f_cfg } =
  cur_func := name;
  clear_alloca ();
  let layout = stack_layout f_param f_cfg in
  let stack_len = 8 * List.length layout in
  let ins = ref [] in

  emit ins (Pushq, [Reg Rbp]);            (* pushq %rbp *)
  emit ins (Movq, [Reg Rsp; Reg Rbp]);    (* movq  $rsp, %rbp *)
  (* emit ins (Pushq, [Reg Rbx]);            push callee-save register *)
  emit ins (Subq, [Imm (Lit (Int64.of_int (stack_len))); Reg Rsp]);    (* Subq $xx, %rsp *)

  (* save parameters to stack frame *)
  let t1 idx name =
    let param_loc = arg_loc idx in
    let cur_frame_loc = List.assoc name layout in

    match param_loc with
      | Reg r -> emit ins (Movq, [param_loc; cur_frame_loc])
      | _ ->
          emit ins (Movq, [param_loc; Reg Rax]);
          emit ins (Movq, [Reg Rax; cur_frame_loc])

  in
  List.iteri t1 f_param;

  (* compile entry block *)
  clear_alloca ();
  let entry = fst f_cfg in
  let i = compile_block {tdecls ; layout} entry in
  emits ins i;
  let entry_elem = [{lbl = name; global = true; asm = (Text !ins);}] in
  ins := [];

  (* compile other blocks *)
  let other_blocks = snd f_cfg in
  let t2 (l: lbl * block): elem = 
    compile_lbl_block (fst l) {tdecls ; layout} (snd l)
  in
  let elems = List.map t2 other_blocks in

  (* exit *)
  emit ins (Addq, [Imm (Lit (Int64.of_int stack_len)); Reg Rsp]);
  (* emit ins (Popq, [Reg Rbx]);  *)
  emit ins (Popq, [Reg Rbp]);
  emit ins (Retq, []);

  let exit_elem = [{lbl = exit_lable !cur_func; global = false; asm = (Text !ins);}] in

  entry_elem @ elems @ exit_elem




(* compile_gdecl ------------------------------------------------------------ *)
(* Compile a global value into an X86 global data declaration and map
   a global uid to its associated X86 label.
*)
let rec compile_ginit = function
  | GNull     -> [Quad (Lit 0L)]
  | GGid gid  -> [Quad (Lbl (Platform.mangle gid))]
  | GInt c    -> [Quad (Lit c)]
  | GString s -> [Asciz s]
  | GArray gs | GStruct gs -> List.map compile_gdecl gs |> List.flatten

and compile_gdecl (_, g) = compile_ginit g


(* compile_prog ------------------------------------------------------------- *)
let compile_prog {tdecls; gdecls; fdecls} : X86.prog =
  let g = fun (lbl, gdecl) -> Asm.data (Platform.mangle lbl) (compile_gdecl gdecl) in
  let f = fun (name, fdecl) -> compile_fdecl tdecls name fdecl in
  (List.map g gdecls) @ (List.map f fdecls |> List.flatten)
