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
          let mut args := e.getAppArgs
          let f     ← TypeChecker.descendExpr (fun f' ↦ mkAppN f' args) (visit e.getAppFn)
          for i in [:args.size] do
            args ← TypeChecker.descendExpr (fun exp ↦ mkAppN f (args.set! i exp)) do
              args.modifyM i visit

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

def Lean.KernelException.toString (e : KernelException) : String := match e with
| .unknownConstant .. => "unknown constant"
| .alreadyDeclared .. => "already declared"
| .declTypeMismatch .. => "decl type mismatch"
| .declHasMVars .. => "decl has mvars"
| .declHasFVars .. => "decl has fvars"
| .funExpected .. => "fun expected"
| .other s => s!"other: {s}"
| .deepRecursion => "deep recursion"
| .deterministicTimeout => "deterministic timeout"
| .excessiveMemory => "excessive memory"
| _ => "x"


structure Traces where
  plain : List String := []
  proofs: List String := []
  explicit: List String := []
  proofs_and_explicit: List String := []
deriving ToJson

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

def LINE_WIDTH := 150

@[command_elab l4lreduce] def elabl4lreduce : CommandElab
  | `(#l4lreduce%$tk $term) => withoutModifyingEnv do
    let (e', tr) ← runTermElabM fun _ => Term.withDeclName `_reduce do
      let e ← Term.elabTerm term none
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← Term.levelMVarToParam (← instantiateMVars e)
      let env ← getEnv
      match TypeChecker.M.run env .safe {} (reduceAndTrace e) with
          | .error ⟨ke, tr⟩ => do
            dbg_trace s!"kernel exception: {ke.toString}"
            pure (none, tr)
          | .ok ⟨e, tr⟩ => pure (e, tr)

    let plain ← do
      modifyScope fun s ↦ s
      runTermElabM fun _ => do
      tr.mapM (fun x ↦ do
        let x' ← Lean.PrettyPrinter.ppExpr x
        pure (Std.Format.pretty x' LINE_WIDTH))

    let with_proofs ← do
      modifyScope fun s ↦ { s with opts := s.opts.set `pp.proofs true }
      runTermElabM fun _ => do
      tr.mapM (fun x ↦ do
        let x' ← Lean.PrettyPrinter.ppExpr x
        pure (Std.Format.pretty x' LINE_WIDTH))

    let explicit ← do
      modifyScope fun s ↦ { s with opts := s.opts.set `pp.explicit true }
      runTermElabM fun _ => do
      tr.mapM (fun x ↦ do
        let x' ← Lean.PrettyPrinter.ppExpr x
        pure (Std.Format.pretty x' LINE_WIDTH))

    let proofs_and_explicit ← do
      modifyScope fun s ↦ { s with opts := (s.opts.set `pp.explicit true).set `pp.proof true }
      runTermElabM fun _ => do
      tr.mapM (fun x ↦ do
        let x' ← Lean.PrettyPrinter.ppExpr x
        pure (Std.Format.pretty x' LINE_WIDTH))

    let mut traces : Traces := ⟨plain, with_proofs, explicit, proofs_and_explicit⟩
    let ppj := Lean.ToJson.toJson traces
    dbg_trace ppj
    if let some e' := e' then
      logInfoAt tk e'
  | _ => throwUnsupportedSyntax

def one_lt_ten : 1 < 10 := Nat.succ_lt_succ (Nat.succ_pos 8)

--- l4lreduce has trouble with this
def decimalDigits : Nat → List Nat
  | 0 => []
  | n + 1 => ((n + 1) % 10 :: decimalDigits ((n + 1) / 10))
decreasing_by exact Nat.div_lt_self (Nat.succ_pos _) one_lt_ten

-- if we add a "gas" parameter, then l4lreduce does just fine.
def decimalDigitsAux : Nat → Nat → List Nat
  | 0, _ => []
  | _, 0 => []
  | m + 1, n => (n % 10 :: decimalDigitsAux m (n / 10))

def decimalDigits' (x : Nat) : List Nat := decimalDigitsAux x x

--#l4lwhnf decimalDigits 104546

--set_option maxHeartbeats 0 in
--#l4lreduce decimalDigits' 123456789

--#l4lreduce [1,2] ++ [3,4]

--set_option maxHeartbeats 0 in
--set_option pp.proofs true in
--set_option pp.explicit true in
--#l4lreduce decimalDigits 1

--#l4lreduce 2 + 2
--#l4lreduce "hello".length


-- #l4lreduce "hello" ++ "world"


-- convert between numeric types...
-- quicksort

def iterate {α : Sort _} (op : α → α) : Nat → α → α
 | 0,          a  => a
 | Nat.succ k, a => iterate op k (op a)

def ackermann : Nat → Nat → Nat
 | 0 => Nat.succ
 | p + 1 => fun n ↦ iterate (ackermann p) n (ackermann p 1)

--#l4lreduce ackermann 1 1

def fib : Nat → Nat
| 0 => 1
| 1 => 1
| n + 2 => fib n + fib (n + 1)

--#l4lreduce fib 10
