import Arith.Types

abbrev Reg := Nat

instance : BEq Reg where
  beq := Nat.beq

instance : Add Reg where
  add := Nat.add

abbrev Accum := Nat
abbrev Flag := Nat
abbrev Mem := Reg -> Nat
abbrev ProgCnt := Nat
abbrev Config := Accum × Flag × ProgCnt × Mem

@[simp] def empty : Mem := fun x => 0

@[simp] def get (r : Reg) (m : Mem) : Nat := m r

@[simp] def set (r : Reg) (n : Nat) (m : Mem) : Mem := fun r' => if r == r' then n else get r' m

@[simp] def first : Reg := 1

@[simp] def next (r : Reg) : Reg := r + 1

@[simp] def rax : Reg := 0

inductive Instr : Type
| mov      : Reg -> Reg -> Instr
| movi     : Reg -> Nat -> Instr
| add      : Reg -> Reg -> Instr
| addi     : Reg -> Nat -> Instr
| sub      : Reg -> Reg -> Instr
| subi     : Reg -> Nat -> Instr
| xor      : Reg -> Nat -> Instr
| and      : Reg -> Nat -> Instr
| sar      : Reg -> Nat -> Instr
| sal      : Reg -> Nat -> Instr
| cmp      : Reg -> Reg -> Instr
| cmpi     : Reg -> Nat -> Instr
| jmp      : Nat -> Instr
| je       : Nat -> Instr
| jne      : Nat -> Instr
| jl       : Nat -> Instr
| jg       : Nat -> Instr
| halt     : Instr
| halteq   : Instr
| haltne   : Instr
| haltg    : Instr
| haltl    : Instr
deriving Repr, BEq

abbrev Prog := List Instr

inductive SmallStep : Instr -> Config -> Config -> Prop
| mov {acc flag i mem} (r1 : Reg) (r2 : Reg):
  SmallStep (Instr.mov r1 r2) (acc, flag, i, mem) (acc, flag, i + 1, set r1 (get r2 mem) mem)
| mov_acc {acc flag i mem} (r1 : Reg) (r2 : Reg) (acond : r1 == rax):
  SmallStep (Instr.mov r1 r2) (acc, flag, i, mem) (get r2 mem, flag, i + 1, mem)

| movi {acc flag i mem} (r1 : Reg) (imm : Nat):
  SmallStep (Instr.movi r1 imm) (acc, flag, i, mem) (acc, flag, i + 1, set r1 imm mem)
| movi_acc {acc flag i mem} (r1 : Reg) (imm : Nat) (acond : r1 == rax):
  SmallStep (Instr.movi r1 imm) (acc, flag, i, mem) (imm, flag, i + 1, mem)

| addi {acc flag i mem} (r1 : Reg) (imm : Nat):
  SmallStep (Instr.addi r1 imm) (acc, flag, i, mem) (acc, flag, i + 1, set r1 ((get r1 mem) + imm) mem)
| addi_acc {acc flag i mem} (r1 : Reg) (imm : Nat) (acond : r1 == rax):
  SmallStep (Instr.addi r1 imm) (acc, flag, i, mem) (acc + imm, flag, i + 1, mem)

| subi {acc flag i mem} (r1 : Reg) (imm : Nat):
  SmallStep (Instr.subi r1 imm) (acc, flag, i, mem) (acc, flag, i + 1, set r1 ((get r1 mem) - imm) mem)
| subi_acc {acc flag i mem} (r1 : Reg) (imm : Nat) (acond : r1 == rax):
  SmallStep (Instr.subi r1 imm) (acc, flag, i, mem) (acc - imm, flag, i + 1, mem)

| add {acc flag i mem} (r1 : Reg) (r2 : Reg):
  SmallStep (Instr.add r1 r2) (acc, flag, i, mem) (acc, flag, i + 1, set r1 ((get r1 mem) + (get r2 mem)) mem)
| add_acc1 {acc flag i mem} (r1 : Reg) (r2 : Reg) (acond : r1 == rax):
  SmallStep (Instr.add r1 r2) (acc, flag, i, mem) (acc + get r2 mem, flag, i + 1, mem)
| add_acc2 {acc flag i mem} (r1 : Reg) (r2 : Reg) (acond : r2 == rax):
  SmallStep (Instr.add r1 r2) (acc, flag, i, mem) (acc, flag, i + 1, set r1 (get r1 mem + acc) mem)

| sub {acc flag i mem} (r1 : Reg) (r2 : Reg):
  SmallStep (Instr.sub r1 r2) (acc, flag, i, mem) (acc, flag, i + 1, set r1 ((get r1 mem) - (get r2 mem)) mem)
| sub_acc1 {acc flag i mem} (r1 : Reg) (r2 : Reg) (acond : r1 == rax):
  SmallStep (Instr.sub r1 r2) (acc, flag, i, mem) (acc - get r2 mem, flag, i + 1, mem)
| sub_acc2 {acc flag i mem} (r1 : Reg) (r2 : Reg) (acond : r2 == rax):
  SmallStep (Instr.sub r1 r2) (acc, flag, i, mem) (acc, flag, i + 1, set r1 (get r1 mem - acc) mem)

| xor_acc {acc flag i mem} (r1 : Reg) (imm : Nat) (acond : r1 == rax):
  SmallStep (Instr.xor r1 imm) (acc, flag, i, mem) (acc ^^^ imm, flag, i + 1, mem)

| and {acc flag i mem} (r1 : Reg) (imm : Nat):
  SmallStep (Instr.and r1 imm) (acc, flag, i, mem) (acc, flag, i + 1, set r1 (get r1 mem &&& imm) mem)
| and_acc {acc flag i mem} (r1 : Reg) (imm : Nat) (acond : r1 == rax):
  SmallStep (Instr.and r1 imm) (acc, flag, i, mem) (acc &&& imm, flag, i + 1, mem)

| sar_acc {acc flag i mem} (r1 : Reg) (imm : Nat) (acond : r1 == rax):
  SmallStep (Instr.sar r1 imm) (acc, flag, i, mem) (acc >>> imm, flag, i + 1, mem)
| sal_acc {acc flag i mem} (r1 : Reg) (imm : Nat) (acond : r1 == rax):
  SmallStep (Instr.sal r1 imm) (acc, flag, i, mem) (acc <<< imm, flag, i + 1, mem)

| cmp_eq_imm {acc flag i mem} (r1 : Reg) (imm : Nat) (acond : (get r1 mem) == imm):
  SmallStep (Instr.cmpi r1 imm) (acc, flag, i, mem) (acc, 0, i + 1, mem)
| cmp_eq_acc_imm {acc flag i mem} (r1 : Reg) (imm : Nat) (acond : acc == imm):
  SmallStep (Instr.cmpi r1 imm) (acc, flag, i, mem) (acc, 0, i + 1, mem)
| cmp_eq_acc {acc flag i mem} (r1 : Reg) (r2 : Reg) (acond : (r1 == rax) ∧ (acc == get r2 mem)):
  SmallStep (Instr.cmp r1 r2) (acc, flag, i, mem) (acc, 0, i + 1, mem)

| cmp_less_imm {acc flag i mem} (r1 : Reg) (imm : Nat) (acond : (get r1 mem) < imm):
  SmallStep (Instr.cmpi r1 imm) (acc, flag, i, mem) (acc, 1, i + 1, mem)
| cmp_less_acc_imm {acc flag i mem} (r1 : Reg) (imm : Nat) (acond : acc < imm):
  SmallStep (Instr.cmpi r1 imm) (acc, flag, i, mem) (acc, 1, i + 1, mem)
| cmp_less_acc {acc flag i mem} (r1 : Reg) (r2 : Reg) (acond : (r1 == rax) ∧ (acc < get r2 mem)):
  SmallStep (Instr.cmp r1 r2) (acc, flag, i, mem) (acc, 1, i + 1, mem)

| cmp_greater_imm {acc flag i mem} (r1 : Reg) (imm : Nat) (acond : (get r1 mem) > imm):
  SmallStep (Instr.cmpi r1 imm) (acc, flag, i, mem) (acc, 1, i + 1, mem)
| cmp_greater_acc_imm {acc flag i mem} (r1 : Reg) (imm : Nat) (acond : acc > imm):
  SmallStep (Instr.cmpi r1 imm) (acc, flag, i, mem) (acc, 1, i + 1, mem)
| cmp_greater_acc {acc flag i mem} (r1 : Reg) (r2 : Reg) (acond : (r1 == rax) ∧ (acc > get r2 mem)):
  SmallStep (Instr.cmp r1 r2) (acc, flag, i, mem) (acc, 1, i + 1, mem)

| jmp {acc flag i mem} (n : Nat):
  SmallStep (Instr.jmp n) (acc, flag, i, mem) (acc, flag, i + n + 1, mem)

| je_true {acc flag i mem} (n : Nat) (fcond : flag == 0):
  SmallStep (Instr.je n) (acc, flag, i, mem) (acc, flag, i + n + 1, mem)
| je_false {acc flag i mem} (n : Nat) (fcond : flag != 0):
  SmallStep (Instr.je n) (acc, flag, i, mem) (acc, flag, i + 1, mem)

| jne_true {acc flag i mem} (n : Nat) (fcond : flag != 0):
  SmallStep (Instr.jne n) (acc, flag, i, mem) (acc, flag, i + n + 1, mem)
| jne_false {acc flag i mem} (n : Nat) (fcond : flag == 0):
  SmallStep (Instr.jne n) (acc, flag, i, mem) (acc, flag, i + 1, mem)

| jl_true {acc flag i mem} (n : Nat) (fcond : flag == 1):
  SmallStep (Instr.jl n) (acc, flag, i, mem) (acc, flag, i + n + 1, mem)
| jl_false {acc flag i mem} (n : Nat) (fcond : flag != 1):
  SmallStep (Instr.jl n) (acc, flag, i, mem) (acc, flag, i + 1, mem)

| jg_true {acc flag i mem} (n : Nat) (fcond : flag == 2):
  SmallStep (Instr.jl n) (acc, flag, i, mem) (acc, flag, i + n + 1, mem)
| jg_false {acc flag i mem} (n : Nat) (fcond : flag != 2):
  SmallStep (Instr.jl n) (acc, flag, i, mem) (acc, flag, i + 1, mem)

| halt {acc flag i mem} :
  SmallStep (Instr.halt) (acc, flag, i, mem) (acc, flag, i, mem)

| halteq_eq {acc flag i mem} (hcond : flag == 0):
  SmallStep (Instr.halteq) (acc, flag, i, mem) (acc, flag, i, mem)
| halteq_ne {acc flag i mem} (hcond : flag != 0):
  SmallStep (Instr.halteq) (acc, flag, i, mem) (acc, flag, i + 1, mem)

| haltne_ne {acc flag i mem} (hcond : flag != 0):
  SmallStep (Instr.haltne) (acc, flag, i, mem) (acc, flag, i, mem)
| haltne_eq {acc flag i mem} (hcond : flag == 0):
  SmallStep (Instr.haltne) (acc, flag, i, mem) (acc, flag, i + 1, mem)

| haltl_eq {acc flag i mem} (hcond : flag == 1):
  SmallStep (Instr.haltl) (acc, flag, i, mem) (acc, flag, i, mem)
| haltl_ne {acc flag i mem} (hcond : flag != 1):
  SmallStep (Instr.haltl) (acc, flag, i, mem) (acc, flag, i + 1, mem)

| haltg_eq {acc flag i mem} (hcond : flag == 2):
  SmallStep (Instr.haltg) (acc, flag, i, mem) (acc, flag, i, mem)
| haltg_ne {acc flag i mem} (hcond : flag != 2):
  SmallStep (Instr.haltg) (acc, flag, i, mem) (acc, flag, i + 1, mem)

inductive exec2 : Prog -> Config -> Config -> Prop
| exec2 {prog instr acc flag mem c'} {i : Nat} (hnth : prog.get? n = some instr) (hstep : SmallStep instr (acc, flag, i, mem) c'):
    exec2 prog (acc, flag, i, mem) c'
