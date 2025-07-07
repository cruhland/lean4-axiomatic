import Lean
import Mathlib.Tactic.GCongr

namespace Lean4Axiomatic.Tactic

open Lean (Expr MVarId Syntax getExprMVarAssignment? withRef)
open Lean.Elab.Tactic (
  Tactic TacticM getMainGoal getMainTarget replaceMainGoal withMainContext
  withRWRulesSeq
)
open Lean.Elab.Term (elabTerm)
open Lean.Meta (
  MetaM isDefEq isProof mkConstWithFreshMVarLevels
  mkFreshExprSyntheticOpaqueMVar saveState withReducible
  withReducibleAndInstances
)
open Lean.MonadEnv (getEnv)
open Lean.MVarId (gcongr gcongrForward)
open Lean.Parser.Tactic (rwRuleSeq)
open Mathlib.Tactic.GCongr (
  gcongrExt gcongrForwardDischarger getCongrAppFnArgs getRel
)

partial def scongr
    (goal : MVarId)
    (mainGoalDischarger : MVarId → MetaM Unit := gcongrForwardDischarger)
    : MetaM (Bool × Array MVarId)
    :=
  goal.withContext do
    try mainGoalDischarger goal; return (true, #[]) catch _ => pure ()
    let rel ← withReducible goal.getType'
    let some (relName, lhs, rhs) := getRel rel
      | throwError "scongr failed, {rel} is not a relation"
    let some (lhsHead, lhsArgs) := getCongrAppFnArgs lhs
      | return (false, #[goal])
    let some (rhsHead, rhsArgs) := getCongrAppFnArgs rhs
      | return (false, #[goal])
    let varyingArgs ← do
      unless lhsHead == rhsHead && lhsArgs.size == rhsArgs.size do
        return (false, #[goal])
      (lhsArgs.zip rhsArgs).mapM λ (lhsArg, rhsArg) => do
        let isSame ← withReducibleAndInstances <| do
          let defEq ← isDefEq lhsArg rhsArg
          return defEq || ((← isProof lhsArg) && (← isProof rhsArg))
        return !isSame
    if varyingArgs.all not then throwError "just rfl should work"
    let s ← saveState
    let mut ex? := none
    let key := { relName, head := lhsHead, varyingArgs }
    for lem in (gcongrExt.getState (← getEnv)).getD key #[] do
      let gs ← try
        let lemRef ← mkConstWithFreshMVarLevels lem.declName
        Except.ok <$> withReducibleAndInstances (goal.apply lemRef)
      catch e => pure (Except.error e)
      match gs with
      | .error e =>
        ex? := ex? <|> (some (← saveState, e))
        s.restore
      | .ok gs =>
        let some e ← getExprMVarAssignment? goal | panic! "unassigned?"
        let args := e.getAppArgs
        let mut subgoals := #[]
        for (i, _j, numHyps) in lem.mainSubgoals do
          let some (.mvar mvarId) := args[i]?
            | panic! "what kind of lemma is this?"
          let (_names2, _vs, mvarId) ←
            mvarId.introsWithBinderIdents [] (maxIntros? := numHyps)
          let (_, subgoals2) ← scongr mvarId mainGoalDischarger
          subgoals := subgoals ++ subgoals2
        let mut out := #[]
        for g in gs do
          out := out.push g
        return (true, out ++ subgoals)
    return (false, #[goal])

/-- Generates the proof needed to rewrite `target` with `rule`. -/
def srewrite (goal : MVarId) (target rule : Expr) : MetaM Expr :=
  goal.withContext do
    goal.checkNotAssigned `srewrite
    let _ ← scongr goal (mainGoalDischarger := gcongrForward #[rule])
    pure target

def srewriteTarget (stx : Syntax) : TacticM Unit :=
  withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let target ← getMainTarget
    dbg_trace f!"target: {target}"
    let expr ← elabTerm stx none
    let srwProof ← srewrite goal target expr
    dbg_trace "srwProof: {srwProof}"
    goal.assign srwProof

syntax (name := srw) "srw " rwRuleSeq : tactic

@[tactic srw] def elabSrw : Tactic := λ stx => do
  let token := stx[0]
  let rulesInBrackets := stx[1]
  let rules := rulesInBrackets[1].getArgs
  let numRules := (rules.size + 1) / 2
  for i in [:numRules] do
    let rule := rules[i * 2]!
    -- Report errors under the rule
    withRef rule do
      let term := rule[1]
      -- The original tactic had a lot of extra code here which I didn't take
      -- the time to understand. Going to try the simplest code path and see
      -- what happens
      srewriteTarget term

end Lean4Axiomatic.Tactic
