inductive Op0 where
  | peekbyte
  | readbyte
deriving Repr

inductive Op1 where
  | add1
  | sub1
  | zeroHuh
  | charHuh
  | inttochar
  | chartoint
  | writeByte
  | eofobjecthuh
  | neg
  | abs
  | inthuh
  | boolhuh
deriving Repr

inductive Op2 where
  | sub
deriving Repr

inductive OpN where
  | add
deriving Repr

abbrev ID := String

inductive Expr where
  | integer (n : Int)
  | boolean (b : Bool)
  | character (c : Char)
  | prim0  (op : Op0)
  | prim1  (op : Op1) (e : Expr)
  | prim2  (op : Op2) (e1 : Expr) (e2 : Expr)
  | primn  (op : OpN) (es : List Expr)
  | letstd (ids : List ID) (es : List Expr) (body : Expr)
  | letstar (ids : List ID) (es : List Expr) (body : Expr)
  | begin  (e1 : Expr) (e2 : Expr)
  | var (id : ID)
deriving Repr
