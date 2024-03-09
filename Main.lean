import «Arith»

def main : IO Unit :=
  IO.println s!"Hello, {eval (Expr.num 5)}!"
