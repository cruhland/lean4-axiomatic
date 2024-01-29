import Lean4Axiomatic.Rational.Exponentiation

/-! # Generic implementation of exponentiation to integers, with properties -/

namespace Lean4Axiomatic.Rational.Impl.Generic

open Lean4Axiomatic.Logic (AP)
open Lean4Axiomatic.Relation.Equivalence (EqvOp)
open Lean4Axiomatic.Relation.Equivalence.Impl.Fn renaming eqvOp → eqvOpFn
open Lean4Axiomatic.Relation.Equivalence.Impl.DepFn renaming eqvOp → eqvOpDepFn

variable
  {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ] [Integer.Induction.{1} ℤ]
  {ℚ : Type}
    [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Negation ℚ]
    [Reciprocation ℚ] [Division ℚ] [Sign ℚ]
    [Natural.Exponentiation ℕ (α := ℚ) (· * ·)]

def FixedIntPowFn (ℚ : Type) [Core (ℤ := ℤ) ℚ] : Type :=
  (p : ℚ) → [AP (p ≄ 0)] → ℚ

def _pow_on_diff (n m : ℕ) : FixedIntPowFn ℚ := λ p => p^n / p^m

local instance fipFn_eqvOp_inst : EqvOp (FixedIntPowFn ℚ) := by
  have : {p : ℚ} → EqvOp ([AP (p ≄ 0)] → ℚ) := eqvOpFn
  have : EqvOp (FixedIntPowFn ℚ) := eqvOpDepFn this
  exact this

theorem _pow_on_diff_subst
    {n₁ m₁ n₂ m₂ : ℕ}
    : (n₁:ℤ) - m₁ ≃ n₂ - m₂ → _pow_on_diff (ℚ := ℚ) n₁ m₁ ≃ _pow_on_diff n₂ m₂
    := by
  intro (_ : (n₁:ℤ) - m₁ ≃ n₂ - m₂)
  show _pow_on_diff n₁ m₁ ≃ _pow_on_diff n₂ m₂
  intro (p : ℚ) (_ : AP (p ≄ 0))
  show p^n₁ / p^m₁ ≃ p^n₂ / p^m₂

  have pow_add_n₁m₂ : p^n₁ * p^m₂ ≃ p^(n₁ + m₂) :=
    Rel.symm Natural.pow_compatL_add
  have pow_add_m₁n₂ : p^m₁ * p^n₂ ≃ p^(m₁ + n₂) :=
    Rel.symm Natural.pow_compatL_add

  have : (n₁:ℤ) + m₂ ≃ n₂ + m₁ :=
    Integer.sub_swap_add.mp ‹(n₁:ℤ) - m₁ ≃ n₂ - m₂›
  have : ((n₁ + m₂:ℕ):ℤ) ≃ ((m₁ + n₂:ℕ):ℤ) := calc
    _ = ((n₁ + m₂:ℕ):ℤ) := rfl
    _ ≃ (n₁:ℤ) + m₂     := AA.compat₂
    _ ≃ n₂ + m₁         := ‹(n₁:ℤ) + m₂ ≃ n₂ + m₁›
    _ ≃ m₁ + n₂         := AA.comm
    _ ≃ ((m₁ + n₂:ℕ):ℤ) := Rel.symm AA.compat₂
  have : n₁ + m₂ ≃ m₁ + n₂ := AA.inject this
  have pow_add_subst : p^(n₁ + m₂) ≃ p^(m₁ + n₂) := Natural.pow_substR this

  have : (p^n₁ / p^m₁) / (p^n₂ / p^m₂) ≃ 1 := calc
    _ = (p^n₁ / p^m₁) / (p^n₂ / p^m₂) := rfl
    _ ≃ (p^n₁ * p^m₂) / (p^m₁ * p^n₂) := div_div_div
    _ ≃ p^(n₁ + m₂) / (p^m₁ * p^n₂)   := div_substL pow_add_n₁m₂
    _ ≃ p^(n₁ + m₂) / p^(m₁ + n₂)     := div_substR pow_add_m₁n₂
    _ ≃ p^(m₁ + n₂) / p^(m₁ + n₂)     := div_substL pow_add_subst
    _ ≃ 1                             := div_same
  have : p^n₁ / p^m₁ ≃ p^n₂ / p^m₂ := div_eqv_1.mp this
  exact this

def ind_ctx : Integer.Induction.ConstData ℤ :=
  Integer.ind_constraints_const (_pow_on_diff_subst (ℚ := ℚ))

def _pow (p : ℚ) [AP (p ≄ 0)] (a : ℤ) : ℚ := ind_ctx.rec_diff a p

/--
TODO

The constraint for `ℤ` to be an integer is needed to ensure that this doesn't
also generate an `Exponentiation.Ops ℚ ℕ`, hiding the `· ^ ·` operator for
natural number exponentiation.
-/
local instance exponentiation_ops : Integer.Exponentiation.Ops ℚ ℤ := {
  _pow := _pow
}

theorem pow_diff
    {p : ℚ} {n m : ℕ} [AP (p ≄ 0)] : p^((n:ℤ) - m) ≃ p^n / p^m
    := by
  let ctx := ind_ctx (ℚ := ℚ)

  have : ctx.rec_diff ((n:ℤ) - m) ≃ ctx.on_diff n m := ctx.rec_diff_eval
  have rec_eval
    : (x : ℚ) → [AP (x ≄ 0)] → ctx.rec_diff ((n:ℤ) - m) x ≃ ctx.on_diff n m x
    := this
  calc
    _ = p^((n:ℤ) - m)              := rfl
    _ = _pow p ((n:ℤ) - m)         := rfl
    _ = ctx.rec_diff ((n:ℤ) - m) p := rfl
    _ ≃ ctx.on_diff n m p          := rec_eval p
    _ = _pow_on_diff n m p         := rfl
    _ = p^n / p^m                  := rfl

/-- TODO -/
theorem pow_substR
    {p : ℚ} [AP (p ≄ 0)] {a₁ a₂ : ℤ} : a₁ ≃ a₂ → p^a₁ ≃ p^a₂
    := by
  intro (_ : a₁ ≃ a₂)
  show p^a₁ ≃ p^a₂
  let ctx := ind_ctx (ℚ := ℚ)

  have : ctx.rec_diff a₁ ≃ ctx.rec_diff a₂ := ctx.rec_diff_subst ‹a₁ ≃ a₂›
  have rec_subst
    : (x : ℚ) → [AP (x ≄ 0)] → ctx.rec_diff a₁ x ≃ ctx.rec_diff a₂ x
    := this
  calc
    _ = p^a₁              := rfl
    _ = _pow p a₁         := rfl
    _ = ctx.rec_diff a₁ p := rfl
    _ ≃ ctx.rec_diff a₂ p := rec_subst p
    _ = _pow p a₂         := rfl
    _ = p^a₂              := rfl

def exponentiation_props :
    Integer.Exponentiation.Props (α := ℚ) (ℤ := ℤ) (· * ·) (· / ·) := {
  pow_diff := pow_diff
  pow_substR := pow_substR
}

def integer_exponentiation :
    Integer.Exponentiation (α := ℚ) (ℤ := ℤ) (· * ·) (· / ·) := {
  toOps := exponentiation_ops
  toProps := exponentiation_props
}

end Lean4Axiomatic.Rational.Impl.Generic
