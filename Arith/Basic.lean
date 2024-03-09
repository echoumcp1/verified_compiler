inductive Op where
  | add
  | sub
  | mul
  | div

inductive Expr where
  | num (n : Int)
  | op  (op : Op) (e1 : Expr) (e2 : Expr)

def eval (e : Expr) : Int := 
  match e with 
  | .num n => n
  | .op op e1 e2 =>
    match op with
    | .add => (eval e1) + (eval e2)
    | .sub => (eval e1) - (eval e2)
    | .mul => (eval e1) * (eval e2)
    | .div => (eval e1) / (eval e2)

