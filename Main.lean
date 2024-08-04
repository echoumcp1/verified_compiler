import «Arith»
open Expr

def main : IO Unit := do
  IO.println s!"interpreted: {interp exampl}"
  match (compile exampl) with
  | Except.ok prog => do
      IO.println (List.map repr prog)
      IO.println s!"compiled: {exec prog}"
  | _ => IO.println ("compile failed :(")
