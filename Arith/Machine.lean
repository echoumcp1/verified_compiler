import Arith.Instrs

open Instr
mutual
  @[simp] def exec1 (prog : Prog) (c : Config) : Prog × Config :=
    match c with
    | (acc, flag, prog_count, mem) => (match prog with
      | [] => (prog, c)
      | (mov r1 0)::ps      => exec1 ps (acc, flag, prog_count + 1, set r1 acc mem)
      | (mov 0 r2)::ps      => exec1 ps (get r2 mem, flag, prog_count + 1, mem)
      | (mov r1 r2)::ps     => exec1 ps (acc, flag, prog_count + 1, set r1 (get r2 mem) mem)
      | (movi 0 imm)::ps    => exec1 ps (imm, flag, prog_count + 1, mem)
      | (movi r1 imm)::ps   => exec1 ps (acc, flag, prog_count + 1, set r1 imm mem)
      | (addi 0 imm)::ps    => exec1 ps (acc + imm, flag, prog_count + 1, mem)
      | (addi r1 imm)::ps   => exec1 ps (acc, flag, prog_count + 1, set r1 ((get r1 mem) + imm) mem)
      | (subi 0 imm)::ps    => exec1 ps (acc - imm, flag, prog_count + 1, mem)
      | (subi r1 imm)::ps   => exec1 ps (acc, flag, prog_count + 1, set r1 ((get r1 mem) - imm) mem)
      | (add 0 r2)::ps      => exec1 ps (acc + get r2 mem, flag, prog_count + 1, mem)
      | (add r1 0)::ps      => exec1 ps (acc, flag, prog_count + 1, set r1 (get r1 mem + acc) mem)
      | (add r1 r2)::ps     => exec1 ps (acc, flag, prog_count + 1, set r1 ((get r1 mem) + (get r2 mem)) mem)
      | (sub 0 r2)::ps      => exec1 ps (acc - get r2 mem, flag, prog_count + 1, mem)
      | (sub r1 0)::ps      => exec1 ps (acc, flag, prog_count + 1, set r1 (get r1 mem - acc) mem)
      | (sub r1 r2)::ps     => exec1 ps (acc, flag, prog_count + 1, set r1 ((get r1 mem) - (get r2 mem)) mem)
      | (Instr.xor rax imm)::ps   => exec1 ps (acc ^^^ imm, flag, prog_count + 1, mem)
      | (Instr.and 0 imm)::ps     => exec1 ps (acc &&& imm, flag, prog_count + 1, mem)
      | (Instr.and r1 imm)::ps    => exec1 ps (acc, flag, prog_count + 1, set r1 (get r1 mem &&& imm) mem)
      | (sar rax imm)::ps   => exec1 ps (acc >>> imm, flag, prog_count + 1, mem)
      | (sal rax imm)::ps   => exec1 ps (acc <<< imm, flag, prog_count + 1, mem)
      | (cmp 0 r2)::ps      =>
          let v := get r2 mem
          let flag' := if (acc == v) then 0 else (if acc < v then 1 else 2)
          exec1 ps (acc, flag', prog_count + 1, mem)
      | (cmp r1 r2)::ps     =>
          let v1 := get r1 mem
          let v2 := get r2 mem
          let flag' := if (v1 == v2) then 0 else (if v1 < v2 then 1 else 2)
          exec1 ps (acc, flag', prog_count + 1, mem)
      | (cmpi 0 imm)::ps    =>
          let flag' := if (acc == imm) then 0 else (if acc < imm then 1 else 2)
          exec1 ps (acc, flag', prog_count + 1, mem)
      | (cmpi r1 imm)::ps   =>
          let v := get r1 mem
          let flag' := if (v == imm) then 0 else (if v < imm then 1 else 2)
          exec1 ps (acc, flag', prog_count + 1, mem)
      | (jmp n)::ps         => jump_forward ps c n
      | (je n)::ps          => if flag == 0 then jump_forward ps c n else exec1 ps (acc, flag, prog_count + 1, mem) -- other instructions
      | (jne n)::ps         => if flag != 0 then jump_forward ps c n else exec1 ps (acc, flag, prog_count + 1, mem)
      | (jl n)::ps          => if flag == 1 then jump_forward ps c n else exec1 ps (acc, flag, prog_count + 1, mem)
      | (jg n)::ps          => if flag == 2 then jump_forward ps c n else exec1 ps (acc, flag, prog_count + 1, mem)
      | halt::ps            => (ps, (acc, flag, prog_count, mem))
      | halteq::ps          => if flag == 0 then (ps, (acc, flag, prog_count, mem)) else exec1 ps (acc, flag, prog_count + 1, mem)
      | haltne::ps          => if flag != 0 then (ps, (acc, flag, prog_count, mem)) else exec1 ps (acc, flag, prog_count + 1, mem)
      | haltl::ps           => if flag == 1 then (ps, (acc, flag, prog_count, mem)) else exec1 ps (acc, flag, prog_count + 1, mem)
      | haltg::ps           => if flag == 2 then (ps, (acc, flag, prog_count, mem)) else exec1 ps (acc, flag, prog_count + 1, mem))
  @[simp] def jump_forward (prog : Prog) (c : Config) (n : Nat) : Prog × Config :=
    match prog, n, c with
    | [], _, _                                            => ([], c)
    | ps, 0, (acc, flag, prog_count, mem)                 => exec1 ps (acc, flag, prog_count + 1, mem)
    | _::ps, Nat.succ n', (acc, flag, prog_count, mem)    => jump_forward ps (acc, flag, prog_count + 1, mem) n'
end

@[simp] def exec (prog : Prog) : Nat :=
  match exec1 prog (0, 0, 0, empty) with
  | ([], c) => c.fst
  | (_, _)  => val_void
