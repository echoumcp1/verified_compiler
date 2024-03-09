inductive Expr where
  | num (n : Int)
  | plus (e1 : Expr) (e2 : Expr)
  | minus (e1 : Expr) (e2 : Expr)
  | mult (e1 : Expr) (e2 : Expr)
  | div (e1 : Expr) (e2 : Expr)

def eval (e : Expr) : Int := 
  match e with 
  | Expr.num n => n
  | Expr.plus e1 e2 => (eval e1) + (eval e2)
  | Expr.minus e1 e2 => (eval e1) - (eval e2)
  | Expr.mult e1 e2 => (eval e1) * (eval e2)
  | Expr.div e1 e2 => (eval e1) / (eval e2)