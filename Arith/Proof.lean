import «Arith».Compile
import «Arith».Eval
import «Arith».Instrs
import «Arith».AST
import Arith.Machine
import Aesop

open Op1

open Lean Parser Tactic

syntax "msimp" (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*) "]")? : tactic

macro_rules
  |`(tactic|msimp) => `(tactic|simp [pure, Except.pure,StateT.pure,bind,Except.bind,StateT.bind,liftM,monadLift,MonadLift.monadLift
  ,StateT.lift, Convertible.valToBits, MonadState.get, MonadStateOf.set])
  |`(tactic|msimp [$t]) => `(tactic|simp [Except.pure,StateT.pure,bind,Except.bind,StateT.bind,liftM,monadLift,MonadLift.monadLift
  ,StateT.lift,Convertible.valToBits,$t])

theorem correctness:
    ∀ (e : _root_.Expr),
      match (compile e) with
      | Except.ok prog => (exec prog = exec (compileBits (interp e)))
      | Except.error _   => interp e = val_void
  | .integer n => by msimp
  | .boolean b => by msimp
  | .character c => by msimp
  | .var x => by msimp
  | .prim1 add1 e1 => by
    induction e1 with
    | integer n =>
      repeat split
      {
        
      }
  | _ => by sorry
