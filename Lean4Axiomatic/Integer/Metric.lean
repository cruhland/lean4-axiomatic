import Lean4Axiomatic.Integer.Order
import Lean4Axiomatic.Metric

/-! # Integer: metric functions -/

namespace Lean4Axiomatic.Integer

open Metric (abs dist MetricSpace)

/-! ## Axioms -/

/-- Metric operations on integers. -/
class Metric.Ops (ℤ : Type) where
  /-- Absolute value. -/
  _abs : ℤ → ℤ

  /-- Distance. -/
  _dist : ℤ → ℤ → ℤ

/-- Enable use of the standard names for absolute value and distance. -/
instance metric_space_inst {ℤ : Type} [Metric.Ops ℤ] : MetricSpace ℤ := {
  abs := Metric.Ops._abs
  dist := Metric.Ops._dist
}

/-- Integer metric operation properties. -/
class Metric.Props
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type)
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Negation ℤ] [Sign ℤ]
      [Ops ℤ]
    where
  /-- Express absolute value in terms of the signum function. -/
  abs_sgn {a : ℤ} : abs a ≃ a * sgn a

export Metric.Props (abs_sgn)

/-- All integer metric axioms. -/
class Metric
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type)
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Negation ℤ] [Sign ℤ]
    where
  toOps : Metric.Ops ℤ
  toProps : Metric.Props ℤ

attribute [instance] Metric.toOps
attribute [instance] Metric.toProps

/-! ## Derived properties -/

variable
  {ℕ : Type} [Natural ℕ]
  {ℤ : Type}
    [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Negation ℤ] [Sign ℤ]
    [Order ℤ] [Metric ℤ] [Subtraction ℤ]

/-- Absolute value is an identity function when its argument is nonnegative. -/
theorem abs_ident {a : ℤ} : a ≥ 0 → abs a ≃ a := by
  intro (_ : a ≥ 0)
  show abs a ≃ a
  have : a > 0 ∨ a ≃ 0 := ge_split.mp ‹a ≥ 0›
  match ‹a > 0 ∨ a ≃ 0› with
  | Or.inl (_ : a > 0) =>
    calc
      _ = abs a     := rfl
      _ ≃ a * sgn a := abs_sgn
      _ ≃ a * 1     := by srw [gt_zero_sgn.mp ‹a > 0›]
      _ ≃ a         := AA.identR
  | Or.inr (_ : a ≃ 0) =>
    calc
      _ = abs a     := rfl
      _ ≃ a * sgn a := abs_sgn
      _ ≃ 0 * sgn a := by srw [‹a ≃ 0›]
      _ ≃ 0         := AA.absorbL
      _ ≃ a         := Rel.symm ‹a ≃ 0›

end Lean4Axiomatic.Integer
