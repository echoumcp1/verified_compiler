import Aesop

inductive instr where
| Push (n : Int)
| Plus
| Minus
deriving Repr

inductive aexp where
  | integer (n : Int)
  | plus (a1 a2 : aexp)
  | minus (a1 a2 : aexp)
  | add1 (a1 : aexp)
  | sub1 (a1 : aexp)
  | neg (a1 : aexp)

@[simp] def aeval (e : aexp) : Int :=
  match e with
  | .integer n => n
  | .plus a1 a2 => (aeval a1) + (aeval a2)
  | .minus a1 a2 => (aeval a1) - (aeval a2)
  | .add1 a1 => (aeval a1) + 1
  | .sub1 a1 => (aeval a1) - 1
  | .neg a1 =>  0 - (aeval a1)

@[simp] def stackExecA (stack : List Int) (prog : List instr) : List Int :=
  match prog with
  | [] => stack
  | .Push n::ps => stackExecA (n::stack) ps
  | .Plus::ps =>
      match stack with
      | n1::n2::xs => stackExecA ((n2 + n1)::xs) ps
      | _ => stackExecA stack ps
  | .Minus::ps =>
      match stack with
      | n1::n2::xs => stackExecA ((n2 - n1)::xs) ps
      | _ => stackExecA stack ps

open instr
open aexp
@[simp] def stackCompile (e : aexp) : List instr :=
  match e with
  | .integer n => [Push n]
  | .plus a1 a2 => (stackCompile a1) ++ (stackCompile a2) ++ [Plus]
  | .minus a1 a2 => (stackCompile a1) ++ (stackCompile a2) ++ [Minus]
  | .add1 a1 => (stackCompile a1) ++ [Push 1, Plus]
  | .sub1 a1 => (stackCompile a1) ++ [Push 1, Minus]
  | .neg a1 => [Push 0] ++ (stackCompile a1) ++ [Minus]

@[simp] theorem executeAppend (p1 p2 : List instr) (stack : List Int) :
  stackExecA stack (p1 ++ p2) = stackExecA (stackExecA stack p1) p2 :=
  by
  induction p1 generalizing p2 stack with
  | nil => rfl
  | cons a p1 IHp1 =>
    cases a <;>
    simp <;>
    repeat (
      cases stack
      case nil => apply IHp1
      case cons _ stack => cases stack <;> try apply IHp1)

theorem stackCompileCorrectH (stack : List Int) (e : aexp) :
  stackExecA stack (stackCompile e) = aeval e :: stack :=
  by induction e generalizing stack <;> simp <;> aesop

theorem stackCompileCorrect (stack : List Int) (e : aexp) :
  stackExecA [] (stackCompile e) = [aeval e] :=
  by apply stackCompileCorrectH
