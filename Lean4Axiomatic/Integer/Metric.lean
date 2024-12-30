import Lean4Axiomatic.Integer.Sign
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

end Lean4Axiomatic.Integer
