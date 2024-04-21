abbrev reg = int

inductive instr : Type
| mov   : reg -> reg -> instr
| movi  : reg -> int -> instr
| add   : reg -> reg -> instr
| sub   : reg -> reg -> instr
| xor   : reg -> reg -> instr
| and   : reg -> reg -> instr
| sar   : reg -> nat -> instr
| sal   : reg -> nat -> instr
| cmp   : reg -> reg -> instr
| jmp   : nat -> instr
| je    : nat -> instr
| jne   : nat -> instr
| jl    : nat -> instr
| jg    : nat -> instr
deriving Repr