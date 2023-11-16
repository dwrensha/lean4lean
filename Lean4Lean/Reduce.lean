import Lean4Lean.TypeChecker
import Lean.Elab.Command
import Lean.Meta.Basic
import Lean.Meta.FunInfo
import Lean.Util.MonadCache

open Lean Lean.Meta Lean.Elab Lean.Elab.Command

partial def reduce' (e : Expr) : TypeChecker.M Expr :=
  let rec visit (e : Expr) : TypeChecker.M Expr := do
        TypeChecker.traceStep e
        let e ← TypeChecker.whnf e
        match e with
        | Expr.app .. =>
          let f     ← visit e.getAppFn
          let mut args  := e.getAppArgs
          for i in [:args.size] do
            --let penc := (←get).enc
            args ← args.modifyM i visit
            --modify fun s ↦ { s with s.enc := fun exp ↦ mkAppFn f }


          if f.isConstOf ``Nat.succ && args.size == 1 && args[0]!.isNatLit then
            return mkRawNatLit (args[0]!.natLit?.get! + 1)
          else
            return mkAppN f args

        | Expr.lam ..        => return e --lambdaTelescope e fun xs b => do mkLambdaFVars xs (← visit b)
        | Expr.forallE ..    => return e --forallTelescope e fun xs b => do mkForallFVars xs (← visit b)
        | Expr.proj n i s .. => return mkProj n i (← visit s)
        | _                  => return e
  visit e

partial def reduceAndTrace (e : Expr) : TypeChecker.M (Expr × List Expr) := do
  let e' ← reduce' e
  pure (e', (← get).trace.reverse)

syntax (name := l4lwhnf) "#l4lwhnf " term : command

@[command_elab l4lwhnf] def elabl4lwhnf : CommandElab
  | `(#l4lwhnf%$tk $term) => withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_reduce do
    let e ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Term.levelMVarToParam (← instantiateMVars e)
    let env ← getEnv
    let e' ← match TypeChecker.M.run env .safe {} (TypeChecker.whnf e) with
          | .error _e => throwError "kernel exception"
          | .ok e => pure e
    logInfoAt tk e'
  | _ => throwUnsupportedSyntax

syntax (name := l4lreduce) "#l4lreduce " term : command

@[command_elab l4lreduce] def elabl4lreduce : CommandElab
  | `(#l4lreduce%$tk $term) => withoutModifyingEnv <| runTermElabM fun _ => Term.withDeclName `_reduce do
    let e ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Term.levelMVarToParam (← instantiateMVars e)
    let env ← getEnv
    let (e', tr) ← match TypeChecker.M.run env .safe {} (reduceAndTrace e) with
          | .error _e => throwError "kernel exception"
          | .ok v => pure v
    for t in tr do
      let p ← Lean.PrettyPrinter.ppExpr t
      dbg_trace p
    logInfoAt tk e'
  | _ => throwUnsupportedSyntax

--- l4lreduce has trouble with this
def decimalDigits : Nat → List Nat
  | 0 => []
  | n + 1 => ((n + 1) % 10 :: decimalDigits ((n + 1) / 10))
decreasing_by exact Nat.div_lt_self (Nat.succ_pos _) (Nat.succ_lt_succ <| Nat.succ_pos 8)

-- if we add a "gas" parameter, then l4lreduce does just fine.
def decimalDigitsAux : Nat → Nat → List Nat
  | 0, _ => []
  | _, 0 => []
  | m + 1, n => (n % 10 :: decimalDigitsAux m (n / 10))

def decimalDigits' (x : Nat) : List Nat := decimalDigitsAux x x

--#l4lwhnf decimalDigits 104546
--#l4lreduce decimalDigits' 4

-- #l4lreduce decimalDigits 134
