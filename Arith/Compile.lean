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

@[simp] def eqImm (imm : Nat) : Prog :=
  [
    cmpi rax imm,
    mov rax val_true,
    je 1,
    mov rax val_false
  ]

@[simp] def compileBits (val : Nat) : Prog :=
  [movi rax val]

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
  | .charToInt => do
      let check <- assertChar rax
      return (
        check ++
       [sar rax char_shift,
        sal rax int_shift])
  | .intToChar => do
      let check <- assertCodepoint rax
      return (
        check ++
       [sar rax int_shift,
        sal rax char_shift,
        xor rax type_char])
  | .neg => do
      let check <- assertInteger rax
      let r <- get
      set (next r)
      return (
        check ++
        [mov r 0,
         sub r rax,
         mov rax r])
  | .abs => do
      let check <- assertInteger rax
      let r <- get
      set (next r)
      return (
        check ++
        [cmpi rax 0,
         jg 3,
         mov r 0,
         sub r rax,
         mov rax r
      ])
  | .not =>
      return [
        cmp rax val_false,
        mov rax val_true,
        je 1,
        mov rax val_false
      ]

def compile_op2 (op: Op2) (prev : Reg): StateT Reg (Except String) Prog :=
  match op with
  | .plus => do
    let check <- assertInteger prev
    let check' <- assertInteger rax
    return (
      check ++
      check' ++
      [add prev rax,
        mov rax prev])
  | .sub => do
    let check <- assertInteger prev
    let check' <- assertInteger rax
    return (
      check ++
      check' ++
      [sub prev rax,
        mov rax prev])
  | .lt => do
    let check <- assertInteger prev
    let check' <- assertInteger rax
    return (
      check ++
      check' ++
      [cmp prev rax,
       mov rax val_true,
       jl 1,
       mov rax val_false]
    )
  | .eq => do
    let check <- assertInteger prev
    let check' <- assertInteger rax
    return (
      check ++
      check' ++
      [cmp prev rax,
       mov rax val_true,
       je 1,
       mov rax val_false]
    )

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
  | .prim2 op e1 e2 => do
      let instrs <- compile_expr e1 c
      let r <- get
      set (next r)
      let instrs' <- compile_expr e2 c
      let instrs'' <- compile_op2 op r
      return (instrs ++ [mov r rax] ++ instrs' ++ instrs'')
  | .if e1 e2 e3 => do
      let instrs <- compile_expr e1 c
      let instrs' <- compile_expr e2 c
      let instrs'' <- compile_expr e3 c
      return (
        instrs ++
        [cmp rax val_false,
        je (List.length instrs' + 1)] ++
        instrs' ++
        [jmp (List.length instrs'')] ++
        instrs''
      )
  | .begin e1 e2 => do
      let instrs <- compile_expr e1 c
      let instrs' <- compile_expr e2 c
      return instrs ++ instrs'
  | .letstd id e body => do
      let instrs <- compile_expr e c
      let r <- get
      set (next r)
      let instrs' <- compile_expr body ((id, r)::c)
      return (instrs ++ [mov r rax] ++ instrs')

@[simp] def compile (e : Expr) : Except String Prog :=
  match (compile_expr e [] first) with
  | .ok res => return res.fst
  | .error _ => throw "compile err"
