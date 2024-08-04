abbrev Reg := Nat
-- def Reg := Nat

-- instance : OfNat Reg 0 where
--   ofNat := Nat.zero

-- instance : OfNat Reg n where
--   ofNat := n

-- instance : Repr Reg where
--   reprPrec : Reg -> Nat -> Std.Format
--   | 0, _ => "rax"
--   | r, _ => "r" ++ (Nat.repr r)

-- instance : ToString Reg where
--   toString : Reg -> String
--   | 0 => "rax"
--   | r => "r" ++ (Nat.repr r)

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
mutual
  @[simp] def exec1 (prog : Prog) (c : Config) : Prog × Config :=
    match c with
    | (acc, flag, mem) => (match prog with
      | [] => (prog, c)
      | (mov r1 0)::ps      => exec1 ps (acc, flag, set r1 acc mem)
      | (mov 0 r2)::ps      => exec1 ps (get r2 mem, flag, mem)
      | (mov r1 r2)::ps     => exec1 ps (acc, flag, set r1 (get r2 mem) mem)
      | (movi 0 imm)::ps    => exec1 ps (imm, flag, mem)
      | (movi r1 imm)::ps   => exec1 ps (acc, flag, set r1 imm mem)
      | (addi 0 imm)::ps    => exec1 ps (acc + imm, flag, mem)
      | (addi r1 imm)::ps   => exec1 ps (acc, flag, set r1 ((get r1 mem) + imm) mem)
      | (subi 0 imm)::ps    => exec1 ps (acc - imm, flag, mem)
      | (subi r1 imm)::ps   => exec1 ps (acc, flag, set r1 ((get r1 mem) - imm) mem)
      | (add 0 r2)::ps      => exec1 ps (acc + get r2 mem, flag, mem)
      | (add r1 0)::ps      => exec1 ps (acc, flag, set r1 (get r1 mem + acc) mem)
      | (add r1 r2)::ps     => exec1 ps (acc, flag, set r1 ((get r1 mem) + (get r2 mem)) mem)
      | (sub 0 r2)::ps      => exec1 ps (acc - get r2 mem, flag, mem)
      | (sub r1 0)::ps      => exec1 ps (acc, flag, set r1 (get r1 mem - acc) mem)
      | (sub r1 r2)::ps     => exec1 ps (acc, flag, set r1 ((get r1 mem) - (get r2 mem)) mem)
      | (Instr.xor rax imm)::ps   => exec1 ps (acc ^^^ imm, flag, mem)
      | (Instr.and 0 imm)::ps     => exec1 ps (acc &&& imm, flag, mem)
      | (Instr.and r1 imm)::ps    => exec1 ps (acc, flag, set r1 (get r1 mem &&& imm) mem)
      | (sar rax imm)::ps   => exec1 ps (acc >>> imm, flag, mem)
      | (sal rax imm)::ps   => exec1 ps (acc <<< imm, flag, mem)
      | (cmp 0 r2)::ps      =>
          let v := get r2 mem
          let flag' := if (acc == v) then 0 else (if acc < v then 1 else 2)
          exec1 ps (acc, flag', mem)
      | (cmp r1 r2)::ps     =>
          let v1 := get r1 mem
          let v2 := get r2 mem
          let flag' := if (v1 == v2) then 0 else (if v1 < v2 then 1 else 2)
          exec1 ps (acc, flag', mem)
      | (cmpi 0 imm)::ps    =>
          let flag' := if (acc == imm) then 0 else (if acc < imm then 1 else 2)
          exec1 ps (acc, flag', mem)
      | (cmpi r1 imm)::ps   =>
          let v := get r1 mem
          let flag' := if (v == imm) then 0 else (if v < imm then 1 else 2)
          exec1 ps (acc, flag', mem)
      | (jmp n)::ps         => jump_forward ps c n
      | (je n)::ps          => if flag == 0 then jump_forward ps c n else exec1 ps (acc, flag, mem) -- other instructions
      | (jne n)::ps         => if flag != 0 then jump_forward ps c n else exec1 ps (acc, flag, mem)
      | (jl n)::ps          => if flag == 1 then jump_forward ps c n else exec1 ps (acc, flag, mem)
      | (jg n)::ps          => if flag == 2 then jump_forward ps c n else exec1 ps (acc, flag, mem)
      | halt::ps            => (ps, (acc, flag, mem))
      | halteq::ps          => if flag == 0 then (ps, (acc, flag, mem)) else exec1 ps (acc, flag, mem)
      | haltne::ps          => if flag != 0 then (ps, (acc, flag, mem)) else exec1 ps (acc, flag, mem)
      | haltl::ps           => if flag == 1 then (ps, (acc, flag, mem)) else exec1 ps (acc, flag, mem)
      | haltg::ps           => if flag == 2 then (ps, (acc, flag, mem)) else exec1 ps (acc, flag, mem))
  @[simp] def jump_forward (prog : Prog) (c : Config) (n : Nat) : Prog × Config :=
    match prog, n with
    | [], _                 => ([], c)
    | ps, 0                 => exec1 ps c
    | _::ps, Nat.succ n'    => jump_forward ps c n'
end

@[simp] def exec (prog : Prog) : Nat :=
  match exec1 prog (0, 0, empty) with
  | ([], c) => c.fst
  | (_, _)  => val_void
