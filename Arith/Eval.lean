import «Arith».AST
import «Arith».Types
open Convertible

inductive Value where
| num (n : Nat)
| bool (b : Bool)
| char (c : Char)

abbrev Env := List (ID × Value)

@[simp] def lookup_env (r : Env) (x : ID) : Except String Value :=
  match r with
  | [] => throw s!"variable {x} not found in environment"
  | (id, v)::rs => if id == x then (return v) else lookup_env rs x

open Value

@[simp] def interpPrim1 (op : Op1) (e : Value) : Except String Value :=
  match op with
  | .add1 =>
      (match e with
      | .num n => return (.num (n + 1))
      | _ => throw s!"add1 requires nat argument")
  | .sub1 =>
    (match e with
      | .num n => return (.num (n - 1))
      | _ => throw s!"sub1 requires nat argument")
  | _ => return (.num 1)

mutual
@[simp] def interp_env (e : Expr) (r : Env) : Except String Value :=
  match e with
  | .integer n => return (num n)
  | .boolean b => return (bool b)
  | .character c => return (char c)
  | .var x => lookup_env r x
  | .prim1 op e => do
      let v <- interp_env e r
      interpPrim1 op v
  | .letstd ids es body => do
      let vs <- interp_star es r
      interp_env body ((List.zip ids vs) ++ r)
  | _ => return (num 1)

@[simp] def interp_star (es : List Expr) (r : Env) : Except String (List Value) :=
  match es with
  | []    => return []
  | e::es => do
    let v <- interp_env e r
    let vs <- interp_star es r
    return (v::vs)
end

@[simp] def interp (e : Expr) : Nat :=
  match interp_env e [] with
  | .error _ => val_void
  | .ok res => (match res with
    | .num n => valToBits n
    | .bool b => valToBits b
    | .char c => valToBits c)
