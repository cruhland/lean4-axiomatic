import Lean4Axiomatic.Integer.Exponentiation
import Lean4Axiomatic.Integer.Impl.Difference.Negation
import Lean4Axiomatic.Integer.Impl.Generic.Subtraction

namespace Lean4Axiomatic.Integer.Impl.Difference

open Logic (AP)
open Relation.Equivalence (EqvOp)

variable
  {α : Type} [EqvOp α] [OfNat α 0] [OfNat α 1] [AP ((1:α) ≄ 0)]
  {mul : α → α → α} [AA.ZeroProduct (α := α) mul]
  {div : α → (y : α) → [AP (y ≄ 0)] → α}
  {ℕ : Type} [Natural ℕ] [pow_nat_inst : Natural.Exponentiation ℕ mul]

/-- TODO -/
def _pow (x : α) [AP (x ≄ 0)] : Difference ℕ → α := by
  intro (n——m)
  show α
  exact div (x^n) (x^m)

local instance exponentiation_ops : Exponentiation.Ops α (Difference ℕ) := {
  _pow := _pow (mul := mul) (div := div)
}

/-- TODO -/
theorem pow_substR
    {x : α} [AP (x ≄ 0)] : {a₁ a₂ : Difference ℕ} → a₁ ≃ a₂ →
    have : Exponentiation.Ops α (Difference ℕ) := exponentiation_ops (mul := mul) (div := div)
    x^a₁ ≃ x^a₂
    := by
  intro (n₁——m₁) (n₂——m₂) (_ : n₁——m₁ ≃ n₂——m₂)
  let pow_ops : Exponentiation.Ops α (Difference ℕ) := exponentiation_ops (mul := mul) (div := div)
  show x^(n₁——m₁) ≃ x^(n₂——m₂)
  calc
    _ = x^(n₁——m₁) := rfl
    _ = div (x^n₁) (x^m₁) := rfl
    --  div
    -- To make progress, need to use properties of division
    -- It would be better at this point to require that `α` is a field
    -- Unfortunately that means abstracting all of the field operations and
    -- properties into a type class, and creating an instance for rational
    -- numbers. I'll need to do this soon anyway, when implementing the real
    -- numbers, but I was hoping it could be avoided here.
    -- Maybe for now I should try to see whether the recursion approach can
    -- be made to work

/-- TODO -/
theorem pow_diff
    {x : α} [AP (x ≄ 0)] {n m : ℕ} :
    have : Exponentiation.Ops α (Difference ℕ) := exponentiation_ops (mul := mul) (div := div)
    x^((n:Difference ℕ) - (m:Difference ℕ)) ≃ div (x^n) (x^m)
    := by
  let pow_ops : Exponentiation.Ops α (Difference ℕ) := exponentiation_ops (mul := mul) (div := div)
  calc
    _ = x^((n:Difference ℕ) - (m:Difference ℕ)) := rfl
    _ ≃ div (x^n) (x^m) := sorry

def exponentiation_props :
    have : Exponentiation.Ops α (Difference ℕ) := exponentiation_ops (mul := mul) (div := div)
    Exponentiation.Props (ℤ := Difference ℕ) mul div
    :=
  Exponentiation.Props.mk (ops_inst := exponentiation_ops (mul := mul) (div := div)) (pow_diff (mul := mul) (div := div)) (pow_substR (mul := mul) (div := div))

def exponentiation : Exponentiation (ℤ := Difference ℕ) mul div := {
  toOps := exponentiation_ops
  toProps := exponentiation_props
}

end Lean4Axiomatic.Integer.Impl.Difference
