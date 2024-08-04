import «Arith».Instrs
import «Arith».AST
import «Arith».Types
open Instr
open Convertible

abbrev Context := List (ID × Reg)

@[simp] def lookup (x : ID) (c : Context) : Except String Reg :=
  match c with
  | [] => throw s!"variable {x} not in context"
  | (var, reg) :: cs => if var == x then (pure reg) else lookup x cs

@[simp] def assertType (mask : Nat) (type : Nat) (r : Reg) : StateT Reg (Except String) Prog := do
  let r' <- get
  set (next r')
  return [
    mov r' r, 
    and r' mask,
    cmpi r' type,
    haltne
  ]

@[simp] def typePred (mask : Nat) (type : Nat) : Prog :=
  [and rax mask, cmpi rax type, mov rax (valToBits true), je 1, mov rax (valToBits false)]

@[simp] def assertInteger := assertType int_mask type_int

@[simp] def assertChar := assertType char_mask type_char

@[simp] def assertCodepoint (r : Reg) : StateT Reg (Except String) Prog := do
  let check <- assertInteger r
  return (
    check ++
   [cmpi r (valToBits 0),
    haltl, 
    cmpi rax (valToBits 1114111),
    haltg, 
    cmpi rax (valToBits 55295),
    jl 3,
    cmpi rax (valToBits 57344),
    jg 1,
    halt 
   ])

@[simp] def compileVal (val : α) [Convertible α] : Prog := 
  [movi rax (valToBits val)]

@[simp] def compile_op1 (op : Op1) : StateT Reg (Except String) Prog :=
  match op with
  | .add1 => do
      let check <- assertInteger rax
      return (check ++ [addi rax (valToBits 1)])
  | .sub1 => do
      let check <- assertInteger rax
      return (check ++ [subi rax (valToBits 1)])
  -- | .zerohuh => do
  --     let check <- assertInteger rax
  --     return (
  --       check ++ 
  --      [cmpi rax 0,
  --       movi rax val_true,
  --       je 1,
  --       movi rax val_false])
  -- | .charhuh => return (typePred char_mask type_char)
  -- | .chartoint => do
  --     let check <- assertChar rax
  --     return (
  --       check ++
  --      [sar rax char_shift,
  --       sal rax int_shift])
  -- | .inttochar => do
  --     let check <- assertCodepoint rax
  --     return (
  --       check ++ 
  --      [sar rax int_shift,
  --       sal rax char_shift,
  --       xor rax type_char])
  -- | .neg => do
  --     let check <- assertInteger rax
  --     let r <- get
  --     set (next r)
  --     return 

  | _ => return []

mutual
@[simp] def compile_expr (e : Expr) (c : Context) : StateT Reg (Except String) Prog :=
  match e with
  | .integer n    => return (compileVal n)
  | .boolean b    => return (compileVal b)
  | .character c  => return (compileVal c)
  | .var x        => do
      let reg <- lookup x c
      return [mov rax reg]
  | .prim1 op e => do
      let instrs <- compile_expr e c
      let instrs' <- compile_op1 op
      return (instrs ++ instrs')
  | .letstd ids es body => do
      let (regs, progs) <- compile_star es c
      let prog <- compile_expr body ((List.zip ids regs) ++ c)
      return (progs ++ prog)
  | _ => return [mov rax 1]

@[simp] def compile_star (es : List Expr) (c : Context) : StateT Reg (Except String) ((List Reg) × Prog) :=
  match es with
  | []    => return ([], [])
  | e::es => do
      let e_instrs <- compile_expr e c
      let r <- get
      set (next r)
      let (rs, es_instrs) <- compile_star es c
      return (r::rs, e_instrs ++ [mov r rax] ++ es_instrs)
end

@[simp] def compile (e : Expr) : Except String Prog :=
  match (compile_expr e [] first) with
  | .ok res => return res.fst
  | .error _ => throw "compile err"
