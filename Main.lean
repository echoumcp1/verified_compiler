import «Arith»
open Expr

def main : IO Unit :=
  match (eval exampl) with
  | .num n => IO.println n
  | _ => IO.println "eval failure"