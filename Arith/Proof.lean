import «Arith».Compile
import «Arith».Eval
import «Arith».Instrs
import «Arith».AST
import Aesop

open Op1

theorem concat_prog:
  ∀ (e : Expr) (prog' : Prog) (config : Config),
    match (compile e) with
    | Except.ok prog => let (_, config') := exec1 prog config
                        exec1 (prog ++ prog') config = exec1 prog' config'
    | Except.error _ => true
  | _ => by sorry

theorem correctness:
    ∀ (e : Expr),
      match (compile e) with
      | Except.ok prog => (exec prog = interp e)
                          --let (prog', (res, _, _)) := exec1 prog (0, 0, empty)
                          --((prog' == []) -> res == interp e) || ((prog' != []) -> interp e == val_void)
      | Except.error _   => interp e = val_void
  | .integer n => by simp [pure, Except.pure, StateT.pure, Convertible.valToBits]
  | .boolean b => by simp [pure, Except.pure, StateT.pure, Convertible.valToBits]
  | .character c => by simp [pure, Except.pure, StateT.pure, Convertible.valToBits]
  | .var x => by simp [Except.pure, StateT.pure,
                      bind, Except.bind, StateT.bind,
                      liftM, monadLift, MonadLift.monadLift, StateT.lift,
                      Convertible.valToBits]
  | _ => by sorry
