inductive Op where
  | add
  | sub
  | mul
  | div
deriving Repr

inductive Expr where
  | num (n : Int)
  | op  (op : Op) (e1 : Expr) (e2 : Expr) 
deriving Repr

def eval (e : Expr) : Expr := 
  match e with 
  | .num n => .num n
  | .op op (.num n1) (.num n2) =>
    match op with
    | .add => .num (n1 + n2)
    | .sub => .num (n1 - n2)
    | .mul => .num (n1 * n2)
    | .div => .num (n1 / n2)
  | .op op (.num n) e => .op op (.num n) (eval e)
  | .op op e1 e2 => .op op (eval e1) e2
  

