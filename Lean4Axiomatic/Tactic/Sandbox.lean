import Lean
import Lean4Axiomatic.Relation.Equivalence
import Mathlib.Tactic.GCongr

namespace Lean4Axiomatic.Tactic

open Lean (Expr MVarId Name Syntax getExprMVarAssignment? withRef)
open Lean.Elab.Tactic (
  Tactic TacticM getMainGoal getMainTarget replaceMainGoal withMainContext
  withRWRulesSeq
)
open Lean.Elab.Term (elabTerm)
open Lean.Meta (
  MetaM isDefEq isProof mkAppM mkConstWithFreshMVarLevels
  mkFreshExprSyntheticOpaqueMVar saveState whnf withReducible
  withReducibleAndInstances
)
open Lean.MonadEnv (getEnv)
open Lean.MVarId (gcongr gcongrForward)
open Lean.Parser.Tactic (rwRuleSeq)
open Mathlib.Tactic.GCongr (
  gcongrExt gcongrForwardDischarger getCongrAppFnArgs getRel
)

def getRel : Expr → Option (Name × Expr × Expr)
| .app (.app rel lhs) rhs => rel.getAppFn.constName?.map (·, lhs, rhs)
| _ => none

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

syntax (name := srwStx) "srw " rwRuleSeq : tactic

@[tactic srwStx] def elabSrw : Tactic := λ stx => do
  let rulesInBrackets := stx[1]
  let rules := rulesInBrackets[1].getArgs
  let rule := rules[0]!

  let symm := !rule[0].isNone
  let term := rule[1]
  let rwRuleExpr ← elabTerm term none
  let directedRuleExpr ←
    if symm then mkAppM ``Rel.symm #[rwRuleExpr] else pure rwRuleExpr

  srw (← getMainGoal) directedRuleExpr

end Lean4Axiomatic.Tactic
