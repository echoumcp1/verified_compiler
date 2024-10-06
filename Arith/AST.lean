import «Arith».Types
open Convertible

inductive Op1 where
  | add1
  | sub1
  | intToChar
  | charToInt
  | neg
  | not
  | abs
deriving Repr

inductive Op2 where
  | plus
  | sub
  | lt
  | eq
deriving Repr

abbrev ID := String

inductive Expr where
  | integer (n : Nat)
  | boolean (b : Bool)
  | character (c : Char)
  | prim1  (op : Op1) (e : Expr)
  | prim2  (op : Op2) (e1 : Expr) (e2 : Expr)
  | letstd (id : ID) (es : Expr) (body : Expr)
  | begin  (e1 : Expr) (e2 : Expr)
  | var (id : ID)
  | if (e1 : Expr) (e2 : Expr) (e3: Expr)

deriving Repr
