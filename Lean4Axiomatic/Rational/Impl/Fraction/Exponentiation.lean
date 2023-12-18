import Lean4Axiomatic.Natural.Impl.Generic
import Lean4Axiomatic.Rational.Impl.Fraction.Sign
import Lean4Axiomatic.Rational.Impl.Fraction.Reciprocation
import Lean4Axiomatic.Rational.Impl.Generic.Exponentiation

namespace Lean4Axiomatic.Rational.Impl.Fraction

open Logic (AP)

variable {ℕ : Type} [Natural ℕ] [Natural.Induction.{1} ℕ]
variable {ℤ : Type} [Integer (ℕ := ℕ) ℤ] [Integer.Induction.{1} ℤ]

local instance natural_exponentiation
    : Natural.Exponentiation ℕ (α := Fraction ℤ) (· * ·)
    :=
  Natural.Impl.Generic.exponentiation

local instance exponentiation_ops : Exponentiation.Ops (Fraction ℤ) ℤ :=
  Generic.exponentiation_ops

-- Hmm, it's no good to use `Fraction ℤ`, when the problem is that we need
-- to represent integers as differences of natural numbers in order to simplify
-- exponentiation. Could there be an alternate form of induction, that uses
-- a substitution principle on natural number differences?
theorem pow_substR
    {p : Fraction ℤ} {a₁ a₂ : ℤ} [AP (p ≄ 0)] : a₁ ≃ a₂ → p^a₁ ≃ p^a₂
    := by
  let motive₁ (x : ℤ) : Prop := {y : ℤ} → x ≃ y → p^x ≃ p^y
  -- Alternative: would having an AsDiff structure solve the subst problem?
  -- If we can get natural number values for the differences, then the rest
  -- of the proof can go through
  have motive₁_subst {x₁ x₂ : ℤ} : x₁ ≃ x₂ → motive₁ x₁ → motive₁ x₂ := by
    intro (_ : x₁ ≃ x₂) (_ : motive₁ x₁)
    intro (y : ℤ) (_ : x₂ ≃ y)
    show p^x₂ ≃ p^y
    have : {y : ℤ} → x₁ ≃ y → p^x₁ ≃ p^y := ‹motive₁ x₁›
    have : p^x₁≃ p^y := this (Rel.trans ‹x₁ ≃ x₂› ‹x₂ ≃ y›)
    have : p^x₂ ≃ p^y := sorry -- Need p^x₁ ≃ p^x₂
    exact this
  have on_diff₁ (n₁ m₁ : ℕ) : motive₁ ((n₁:ℤ) - m₁) := by
    let x := (n₁:ℤ) - m₁
    intro (y : ℤ)
    show ((n₁:ℤ) - m₁) ≃ y → p^((n₁:ℤ) - m₁) ≃ p^y
    let motive₂ (z : ℤ) : Prop := x ≃ z → p^x ≃ p^z
    have motive₂_subst {z₁ z₂ : ℤ} : z₁ ≃ z₂ → motive₂ z₁ → motive₂ z₂ := by
      intro (_ : z₁ ≃ z₂) (_ : motive₂ z₁)
      show motive₂ z₂
      have : x ≃ z₁ → p^x ≃ p^z₁ := ‹motive₂ z₁›
      have : x ≃ z₂ → p^x ≃ p^z₂ := by
        intro (_ : x ≃ z₂)
        show p^x ≃ p^z₂
        have : z₁ ≃ x := Rel.trans ‹z₁ ≃ z₂› (Rel.symm ‹x ≃ z₂›)
        have : {y : ℤ} → z₁ ≃ y → p^z₁ ≃ p^y := by
          intro (y : ℤ) (_ : z₁ ≃ y)
          show p^z₁ ≃ p^y
          -- This proof won't go through. Maybe this whole theorem needs to be
          -- assumed as an axiom. Unless I missed something?
          admit
        have : motive₁ z₁ := this
        have : motive₁ x := motive₁_subst ‹z₁ ≃ x› ‹motive₁ z₁›
        have : {y : ℤ} → x ≃ y → p^x ≃ p^y := this
        have : p^x ≃ p^z₂ := this ‹x ≃ z₂›
        exact this
      have : motive₂ z₂ := this
      exact this
    have on_diff₂ (n₂ m₂ : ℕ) : motive₂ ((n₂:ℤ) - m₂) := by
      let z := (n₂:ℤ) - m₂
      intro (_ : x ≃ z)
      show p^x ≃ p^z

      let a₁ := (n₁:ℤ); let a₂ := (n₂:ℤ); let b₁ := (m₁:ℤ); let b₂ := (m₂:ℤ)
      have : a₁ - b₁ ≃ a₂ - b₂ := ‹x ≃ z›
      have : a₁ + b₂ ≃ a₂ + b₁ := Integer.sub_swap_add.mp this
      have : (((n₁ + m₂):ℕ):ℤ) ≃ (((m₁ + n₂):ℕ):ℤ) := calc
        _ ≃ (((n₁ + m₂):ℕ):ℤ) := Rel.refl
        _ ≃ (n₁:ℤ) + (m₂:ℤ)   := AA.compat₂
        _ ≃ a₁ + b₂           := Rel.refl
        _ ≃ a₂ + b₁           := ‹a₁ + b₂ ≃ a₂ + b₁›
        _ ≃ b₁ + a₂           := AA.comm
        _ ≃ (m₁:ℤ) + (n₂:ℤ)   := Rel.refl
        _ ≃ (((m₁ + n₂):ℕ):ℤ) := Rel.symm AA.compat₂
      have : n₁ + m₂ ≃ m₁ + n₂ := AA.inject this

      have pow_add_n₁m₂ : p^n₁ * p^m₂ ≃ p^(n₁ + m₂) :=
        Rel.symm Natural.pow_compatL_add
      have pow_add_m₁n₂ : p^m₁ * p^n₂ ≃ p^(m₁ + n₂) :=
        Rel.symm Natural.pow_compatL_add
      have pow_add_subst : p^(n₁ + m₂) ≃ p^(m₁ + n₂) :=
        Natural.pow_substR ‹n₁ + m₂ ≃ m₁ + n₂›
      have : p^(a₁ - b₁) / p^(a₂ - b₂) ≃ 1 := calc
        _ ≃ p^(a₁ - b₁) / p^(a₂ - b₂)     := eqv_refl
        _ ≃ (p^n₁ / p^m₁) / p^(a₂ - b₂)   := div_substL pow_diff
        _ ≃ (p^n₁ / p^m₁) / (p^n₂ / p^m₂) := div_substR pow_diff
        _ ≃ (p^n₁ * p^m₂) / (p^m₁ * p^n₂) := div_div_div
        _ ≃ p^(n₁ + m₂) / (p^m₁ * p^n₂)   := div_substL pow_add_n₁m₂
        _ ≃ p^(n₁ + m₂) / p^(m₁ + n₂)     := div_substR pow_add_m₁n₂
        _ ≃ p^(m₁ + n₂) / p^(m₁ + n₂)     := div_substL pow_add_subst
        _ ≃ 1                             := div_same

      have : p^(a₁ - b₁) ≃ p^(a₂ - b₂) := div_eqv_1.mp this
      have : p^x ≃ p^z := this
      exact this

  apply Integer.ind_diff_on a₁
  intro (n₁ : ℕ) (m₁ : ℕ)
  let motive₂ (x₂ : ℤ) : Prop := x₁ ≃ x₂ → p^x₁ ≃ p^x₂
  apply Integer.ind_diff_on a₂
  intro (n₂ : ℕ) (m₂ : ℕ)
  let a₁ := (n₁:ℤ); let a₂ := (n₂:ℤ); let b₁ := (m₁:ℤ); let b₂ := (m₂:ℤ)
  intro (_ : a₁ - b₁ ≃ a₂ - b₂)
  show p^(a₁ - b₁) ≃ p^(a₂ - b₂)

  have : a₁ + b₂ ≃ a₂ + b₁ := Integer.sub_swap_add.mp ‹a₁ - b₁ ≃ a₂ - b₂›
  have : (((n₁ + m₂):ℕ):ℤ) ≃ (((m₁ + n₂):ℕ):ℤ) := calc
    _ ≃ (((n₁ + m₂):ℕ):ℤ) := Rel.refl
    _ ≃ (n₁:ℤ) + (m₂:ℤ)   := AA.compat₂
    _ ≃ a₁ + b₂           := Rel.refl
    _ ≃ a₂ + b₁           := ‹a₁ + b₂ ≃ a₂ + b₁›
    _ ≃ b₁ + a₂           := AA.comm
    _ ≃ (m₁:ℤ) + (n₂:ℤ)   := Rel.refl
    _ ≃ (((m₁ + n₂):ℕ):ℤ) := Rel.symm AA.compat₂
  have : n₁ + m₂ ≃ m₁ + n₂ := AA.inject this

  have : p^n₁ * p^m₂ ≃ p^(n₁ + m₂) := Rel.symm Natural.pow_compatL_add
  have : p^m₁ * p^n₂ ≃ p^(m₁ + n₂) := Rel.symm Natural.pow_compatL_add
  have : p^(n₁ + m₂) ≃ p^(m₁ + n₂) := Natural.pow_substR ‹n₁ + m₂ ≃ m₁ + n₂›
  have : p^(a₁ - b₁) / p^(a₂ - b₂) ≃ 1 := calc
    _ ≃ p^(a₁ - b₁) / p^(a₂ - b₂)     := eqv_refl
    _ ≃ (p^n₁ / p^m₁) / p^(a₂ - b₂)   := div_substL pow_diff
    _ ≃ (p^n₁ / p^m₁) / (p^n₂ / p^m₂) := div_substR pow_diff
    _ ≃ (p^n₁ * p^m₂) / (p^m₁ * p^n₂) := div_div_div
    _ ≃ p^(n₁ + m₂) / (p^m₁ * p^n₂)   := div_substL ‹p^n₁ * p^m₂ ≃ p^(n₁ + m₂)›
    _ ≃ p^(n₁ + m₂) / p^(m₁ + n₂)     := div_substR ‹p^m₁ * p^n₂ ≃ p^(m₁ + n₂)›
    _ ≃ p^(m₁ + n₂) / p^(m₁ + n₂)     := div_substL ‹p^(n₁ + m₂) ≃ p^(m₁ + n₂)›
    _ ≃ 1                             := div_same

  have : p^(a₁ - b₁) ≃ p^(a₂ - b₂) := div_eqv_1.mp this
  exact this

def exponentiation_props : Exponentiation.Props (Fraction ℤ) := {
  pow_diff := Generic.pow_diff
  pow_substR := pow_substR
}

def integer_exponentiation : Exponentiation (Fraction ℤ) := {
  toOps := exponentiation_ops
  toProps := exponentiation_props
}

end Lean4Axiomatic.Rational.Impl.Fraction
