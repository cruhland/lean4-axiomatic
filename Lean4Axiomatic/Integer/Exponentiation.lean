import Lean4Axiomatic.Integer.Subtraction

/-! # Exponentiation to an integer -/

namespace Lean4Axiomatic.Integer

open Logic (AP)
open Relation.Equivalence (EqvOp)

/-! ## Axioms -/

/-- Operations for raising numeric values to integer powers. -/
class Exponentiation.Ops (α : Type) [EqvOp α] [OfNat α 0] (ℤ : Type) :=
  /-- Exponentiation to an integer power. -/
  _pow (x : α) [AP (x ≄ 0)] : ℤ → α

/-- Enables the use of the `· ^ ·` operator for exponentiation. -/
infixr:80 " ^ " => Exponentiation.Ops._pow

/-- Properties of exponentiation to an integer. -/
class Exponentiation.Props
    {α : Type} [EqvOp α] [OfNat α 0] [OfNat α 1] [AP ((1:α) ≄ 0)]
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type}
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    (mul : (α → α → α)) [AA.ZeroProduct (α := α) mul]
    (div : (α → (y : α) → [AP (y ≄ 0)] → α))
    [Natural.Exponentiation ℕ mul] [ops_inst : Ops α ℤ]
    :=
  /-- TODO -/
  pow_diff {x : α} [AP (x ≄ 0)] {n m : ℕ} : x^((n:ℤ) - (m:ℤ)) ≃ div (x^n) (x^m)

  /-- TODO -/
  pow_substR {x : α} [AP (x ≄ 0)] {a₁ a₂ : ℤ} : a₁ ≃ a₂ → x^a₁ ≃ x^a₂

export Exponentiation.Props (pow_diff pow_substR)

/-- All exponentiation axioms. -/
class Exponentiation
    {α : Type} [EqvOp α] [OfNat α 0] [OfNat α 1] [AP ((1:α) ≄ 0)]
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type}
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    (mul : (α → α → α)) [AA.ZeroProduct (α := α) mul]
    (div : outParam (α → (y : α) → [AP (y ≄ 0)] → α))
    [Natural.Exponentiation ℕ mul]
    :=
  toOps : Exponentiation.Ops α ℤ
  toProps : Exponentiation.Props (ℤ := ℤ) mul div

attribute [instance] Exponentiation.toOps
attribute [instance] Exponentiation.toProps

/-! ## Derived properties -/

end Lean4Axiomatic.Integer
