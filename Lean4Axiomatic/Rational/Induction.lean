import Lean4Axiomatic.Function
import Lean4Axiomatic.Rational.Reciprocation

/-!
# Rational induction

See `Lean4Axiomatic.Integer.Induction` for a detailed explanation of the
concepts.
-/

namespace Lean4Axiomatic.Rational

open Function (IndexedFamily fsubst)
open Logic (AP)
open Relation.Equivalence (EqvOp)

/-! ## Axioms -/

/--
Provides "handler" functions for the structures traversed during induction.
-/
class Induction.Context
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    {ℚ : Type} [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    [Reciprocation ℚ] [Division ℚ] (motive : ℚ → Sort u) [IndexedFamily motive]
    :=
  /-- Handler for a ratio of integers (this is the only one for rationals). -/
  on_ratio (a b : ℤ) [AP (b ≄ 0)] : motive (a / b)

  /-- The `on_ratio` handler respects equivalence of ratios. -/
  on_ratio_subst
    {a₁ b₁ a₂ b₂ : ℤ} [AP (b₁ ≄ 0)] [AP (b₂ ≄ 0)]
    {ratio_eqv : (a₁:ℚ) / b₁ ≃ a₂ / b₂ }
    : fsubst ratio_eqv (on_ratio a₁ b₁) ≃ on_ratio a₂ b₂

/-- The fundamental induction operations on rational numbers. -/
class Induction.Ops
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    [Reciprocation ℚ] [Division ℚ]
    :=

  /--
  Induction principle for rational numbers: if a property holds for all ratios
  of two integers, then it holds for all rational numbers.
  -/
  ind_ratio
    {motive : ℚ → Sort u} [IndexedFamily motive] (ctx : Context motive) (p : ℚ)
    : motive p

/--
Convenience function that enables using `ctx.ind_ratio` instead of
`ind_ratio ctx`.
-/
def Induction.Context.ind_ratio
    {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    {ℚ : Type} [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    [Reciprocation ℚ] [Division ℚ] [Ops ℚ]
    {motive : ℚ → Sort u} [IndexedFamily motive]
    : (ctx : Context motive) → (p : ℚ) → motive p
    :=
  Ops.ind_ratio

/-- Properties of rational induction operations. -/
class Induction.Props
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    [Reciprocation ℚ] [Division ℚ] [Ops ℚ]
    :=
  /-- The computational behavior of rational number induction. -/
  ind_ratio_eval
    {motive : ℚ → Sort u} [IndexedFamily motive] (ctx : Context motive)
    {a b : ℤ} [AP (b ≄ 0)] : ctx.ind_ratio (a / b) ≃ ctx.on_ratio a b

  /-- Rational number induction respects equivalence. -/
  ind_ratio_subst
    {motive : ℚ → Sort u} [IndexedFamily motive] {ctx : Context motive}
    {p₁ p₂ : ℚ} {p_eqv : p₁ ≃ p₂}
    : fsubst ‹p₁ ≃ p₂› (ctx.ind_ratio p₁) ≃ ctx.ind_ratio p₂

/-- All rational number induction axioms. -/
class Induction
    {ℕ ℤ : outParam Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ]
    [Reciprocation ℚ] [Division ℚ]
    :=
  toOps : Induction.Ops ℚ
  toProps : Induction.Props ℚ

attribute [instance] Induction.toOps
attribute [instance] Induction.toProps

-- TODO: Derived properties

end Lean4Axiomatic.Rational
