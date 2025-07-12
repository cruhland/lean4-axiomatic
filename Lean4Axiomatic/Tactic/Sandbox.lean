import Lean
import Lean4Axiomatic.Relation.Equivalence
import Mathlib.Tactic.GCongr

namespace Lean4Axiomatic.Tactic

open Lean (Expr MVarId Name Syntax getExprMVarAssignment? registerTraceClass)
open Lean.Elab (throwAbortTactic)
open Lean.Elab.Tactic (Tactic TacticM elabTerm getMainGoal)
open Lean.Meta (
  isDefEq inferType isProof mkAppM mkFreshExprMVar saveState withReducible
)
open Lean.MonadEnv (getEnv)
open Lean.MVarId (gcongr gcongrForward)
open Lean.Parser.Tactic (rwRuleSeq)
open Mathlib.Tactic.GCongr (
  gcongrExt gcongrForwardDischarger getCongrAppFnArgs getRel
)

initialize registerTraceClass `Meta.srw

partial def
    srw (goal : MVarId) (rwRule : Expr) : TacticM Unit
    := goal.withContext do
  /- Try to solve goal right away -/
  try
    goal.gcongrForward #[rwRule]
    return ()
  catch _ =>
    pure ()

  /- Validate goal is in the right shape for this tactic -/
  -- Use `getType'` instead of `getType` to resolve mvars and reduce exprs
  -- But only use reducible transparency to avoid unfolding too much
  let rel ← withReducible goal.getType'
  let some (relName, lhs, rhs) := getRel rel | throwError "not rel"
  let some (lhsHead, lhsArgs) := getCongrAppFnArgs lhs | throwError "lhs bad"
  let some (rhsHead, rhsArgs) := getCongrAppFnArgs rhs | throwError "rhs bad"
  unless lhsHead == rhsHead && lhsArgs.size == rhsArgs.size do
    throwError "mismatched lhs & rhs"
  let varyingArgs ← (lhsArgs.zip rhsArgs).mapM λ (lhsArg, rhsArg) => do
    let argsEq ← isDefEq lhsArg rhsArg
    -- Considering proofs equal may need to be updated
    let isSame := argsEq || (← isProof lhsArg) && (← isProof rhsArg)
    return !isSame
  if varyingArgs.all not then throwError "args are all same; use rfl instead?"

  /- Apply the first lemma that matches -/
  let key := { relName, head := lhsHead, varyingArgs }
  let matchingLemmas := (gcongrExt.getState (← getEnv)).getD key #[]
  let s ← saveState
  let lemAndNewGoalsOpt ← matchingLemmas.findSomeM? λ lem =>
    try
      let gs ← goal.apply (.const lem.declName [])
      return some (lem, gs)
    catch _ =>
      s.restore
      return none
  let some (lem, _newGoals) := lemAndNewGoalsOpt | return ()

  /- Recursively apply this tactic to main subgoals -/
  let some e ← getExprMVarAssignment? goal | panic! "goal unassigned?"
  let args := e.getAppArgs
  for (i, _, _) in lem.mainSubgoals do
    let some (.mvar mvarId) := args[i]? | panic! "hyp not an mvar?"
    srw mvarId rwRule

def elabTermStx (term : Syntax) : TacticM Expr := do
  let expr ← elabTerm term (expectedType? := none) (mayPostpone := true)
  if expr.hasSyntheticSorry then
    -- Elaboration can produce `sorry` to indicate failure
    throwAbortTactic
  return expr

def elabRules (rulesInBrackets : Syntax) : TacticM Expr := do
  let rules := rulesInBrackets[1].getArgs
  let rule := rules[0]!
  let symm := !rule[0].isNone
  let term := rule[1]

  let rwRuleExpr ← elabTermStx term
  if symm then mkAppM ``Rel.symm #[rwRuleExpr] else pure rwRuleExpr

syntax (name := srwStx) "srw " rwRuleSeq : tactic

@[tactic srwStx] def elabSrw : Tactic := λ stx => do
  let goal ← getMainGoal
  goal.withContext do
    let directedRuleExpr ← elabRules stx[1]
    srw goal directedRuleExpr

partial def frw (goal : MVarId) (fnArg rwRule : Expr) : TacticM Unit := do
  /- Create a subgoal metavariable for the function. We must give it an
     explicit type: Lean isn't able to figure it out.
  -/
  let fnArgType ← inferType fnArg
  let goalType ← withReducible goal.getType'
  let fnGoalType := .forallE `x fnArgType goalType .default
  let fn ← mkFreshExprMVar (some fnGoalType)

  goal.assign (.app fn fnArg)
  srw fn.mvarId! rwRule

syntax (name := frwStx) "frw " rwRuleSeq term : tactic

@[tactic frwStx] def elabFrw : Tactic := λ stx => do
  let goal ← getMainGoal
  goal.withContext do
    let directedRuleExpr ← elabRules stx[1]
    let fnArg ← elabTermStx stx[2]
    frw goal fnArg directedRuleExpr

end Lean4Axiomatic.Tactic
