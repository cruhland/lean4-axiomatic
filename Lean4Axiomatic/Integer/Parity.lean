import Lean4Axiomatic.Integer.Division

/-! # Integer parity (evenness and oddness) -/

namespace Lean4Axiomatic.Integer

open Lean4Axiomatic.Logic (Either)
open Lean4Axiomatic.Metric (abs)

/-! ## Axioms -/

class Parity.Ops (α : Type) where
  Even (x : α) : Prop

  Odd (x : α) : Prop

export Parity.Ops (Even Odd)

class Parity.Props
    {ℕ : Type} [Natural ℕ]
    (ℤ : Type)
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Order ℤ] [Negation ℤ]
      [Sign ℤ] [Metric ℤ] [Division ℤ] [Ops ℤ]
    where
  even_rem {a : ℤ} : Even a ↔ (div_floored a 2).remainder ≃ 0
  odd_rem {a : ℤ} : Odd a ↔ (div_floored a 2).remainder ≃ 1

class Parity
    {ℕ : Type} [Natural ℕ]
    (ℤ : Type)
      [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Order ℤ] [Negation ℤ]
      [Sign ℤ] [Metric ℤ] [Division ℤ] where
  toOps : Parity.Ops ℤ
  toProps : Parity.Props ℤ

attribute [instance] Parity.toOps
attribute [instance] Parity.toProps

/-! ## Derived properties -/

variable
  {ℕ : Type} [Natural ℕ]
  {ℤ : Type}
    [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ] [Order ℤ] [Negation ℤ]
    [Sign ℤ] [Metric ℤ] [Division ℤ] [Subtraction ℤ]
    [Natural.Exponentiation ℕ ℤ] [Parity ℤ]

def even_to_witness {a : ℤ} : Even a → { b : ℤ // a ≃ 2 * b } := sorry
def half {a : ℤ} : Even a → ℤ := sorry
theorem even_eqv {a : ℤ} (e : Even a) : a ≃ 2 * half e := sorry
def even_from_witness {a b : ℤ} : a ≃ 2 * b → Even a := sorry

def odd_to_witness {a : ℤ} : Odd a → { b : ℤ // a ≃ 2 * b + 1 } := sorry
def half_floored {a : ℤ} : Odd a → ℤ := sorry
theorem odd_eqv {a : ℤ} (odd : Odd a) : a ≃ 2 * half_floored odd + 1 := sorry
def odd_from_witness {a b : ℤ} : a ≃ 2 * b + 1 → Odd a := sorry

@[gcongr]
theorem half_subst
    {a₁ a₂ : ℤ} {e₁ : Even a₁} {e₂ : Even a₂} : a₁ ≃ a₂ → half e₁ ≃ half e₂
    := by
  intro (_ : a₁ ≃ a₂)
  show half e₁ ≃ half e₂

  have : 2 * half e₁ ≃ 2 * half e₂ := calc
    _ = 2 * half e₁ := rfl
    _ ≃ a₁          := Rel.symm (even_eqv e₁)
    _ ≃ a₂          := ‹a₁ ≃ a₂›
    _ ≃ 2 * half e₂ := even_eqv e₂
  have : half e₁ ≃ half e₂ :=
    mul_cancelL two_neqv_zero ‹2 * half e₁ ≃ 2 * half e₂›
  exact this

/-- Every integer is either even or odd, but not both. -/
def parity (a : ℤ) : AA.ExactlyOneOfTwo₁ (Even a) (Odd a) :=
  have : (1:ℤ) > 0 := zero_lt_one
  have : (2:ℤ) > 0 := Trans.trans two_gt_one ‹(1:ℤ) > 0›
  have : (2:ℤ) ≥ 0 := ge_split.mpr (.inl ‹(2:ℤ) > 0›)

  have : Either (Even a) (Odd a) :=
    let d := div_floored a 2
    let q := d.quotient; let r := d.remainder

    have : Either (r ≃ 0) (r ≃ 1) :=
      have : r * 2 ≥ 0 * 2 := calc
        _ = r * 2 := rfl
        _ ≥ 0     := d.rem_sgn
        _ ≃ 0 * 2 := Rel.symm AA.absorbL
      have : r ≥ 0 := mul_cancelR_le ‹(2:ℤ) > 0› ‹r * 2 ≥ 0 * 2›
      have : Either (r ≃ 0) (r > 0) := (ge_split_either ‹r ≥ 0›).swap
      match ‹Either (r ≃ 0) (r > 0)› with
      | .inl (_ : r ≃ 0) =>
        show Either (r ≃ 0) (r ≃ 1) from .inl ‹r ≃ 0›
      | .inr (_ : r > 0) =>
        have : r ≥ 1 := pos_gt_iff_ge.mp ‹r > 0›
        have : Either (r ≃ 1) (r > 1) := (ge_split_either ‹r ≥ 1›).swap
        match ‹Either (r ≃ 1) (r > 1)› with
        | .inl (_ : r ≃ 1) =>
          show Either (r ≃ 0) (r ≃ 1) from .inr ‹r ≃ 1›
        | .inr (_ : r > 1) =>
          have : r ≥ 2 := calc
            _ = r     := rfl
            _ ≥ 1 + 1 := lt_iff_le_incL.mp ‹r > 1›
            _ ≃ 2     := add_one_one
          have : r < 2 := calc
            _ = r     := rfl
            _ ≃ abs r := Rel.symm (abs_ident ‹r ≥ 0›)
            _ < abs 2 := d.rem_mag
            _ ≃ 2     := abs_ident ‹(2:ℤ) ≥ 0›
          show Either (r ≃ 0) (r ≃ 1) from (lt_ge_false ‹r < 2› ‹r ≥ 2›).elim

    match ‹Either (r ≃ 0) (r ≃ 1)› with
    | .inl (_ : r ≃ 0) =>
      have : a ≃ 2 * q := calc
        _ = a         := rfl
        _ ≃ 2 * q + r := d.div_eqv
        _ ≃ 2 * q + 0 := by srw [‹r ≃ 0›]
        _ ≃ 2 * q     := AA.identR
      have : Even a := even_from_witness ‹a ≃ 2 * q›
      show Either (Even a) (Odd a) from .inl ‹Even a›
    | .inr (_ : r ≃ 1) =>
      have : a ≃ 2 * q + 1 := calc
        _ = a         := rfl
        _ ≃ 2 * q + r := d.div_eqv
        _ ≃ 2 * q + 1 := by srw [‹r ≃ 1›]
      have : Odd a := odd_from_witness ‹a ≃ 2 * q + 1›
      show Either (Even a) (Odd a) from .inr ‹Odd a›

  have : ¬(Even a ∧ Odd a) := λ (And.intro (_ : Even a) (_ : Odd a)) =>
    let even_div : FlooredDivision a 2 :=
      let b := half ‹Even a›
      have : a ≃ 2 * b + 0 := calc
        _ = a         := rfl
        _ ≃ 2 * b     := even_eqv ‹Even a›
        _ ≃ 2 * b + 0 := Rel.symm AA.identR
      have : abs (0:ℤ) < abs 2 := calc
        _ = abs (0:ℤ) := rfl
        _ ≃ 0         := abs_ident le_refl
        _ < 2         := ‹(2:ℤ) > 0›
        _ ≃ abs 2     := Rel.symm (abs_ident ‹(2:ℤ) ≥ 0›)
      have : (0:ℤ) * 2 ≥ 0 := calc
        _ = (0:ℤ) * 2 := rfl
        _ ≃ 0         := AA.absorbL
        _ ≥ 0         := le_refl
      show FlooredDivision a 2 from {
        quotient := b
        remainder := 0
        div_eqv := ‹a ≃ 2 * b + 0›
        rem_mag := ‹abs (0:ℤ) < abs 2›
        rem_sgn := ‹(0:ℤ) * 2 ≥ 0›
      }

    let odd_div : FlooredDivision a 2 :=
      let c := half_floored ‹Odd a›
      have : a ≃ 2 * c + 1 := odd_eqv ‹Odd a›
      have : (1:ℤ) ≥ 0 := ge_split.mpr (.inl zero_lt_one)
      have : abs (1:ℤ) < abs 2 := calc
        _ = abs (1:ℤ) := rfl
        _ ≃ 1         := abs_ident ‹(1:ℤ) ≥ 0›
        _ < 2         := two_gt_one
        _ ≃ abs 2     := Rel.symm (abs_ident ‹(2:ℤ) ≥ 0›)
      have : (1:ℤ) * 2 ≥ 0 := calc
        _ = (1:ℤ) * 2 := rfl
        _ ≃ 2         := AA.identL
        _ ≥ 0         := ‹(2:ℤ) ≥ 0›
      show FlooredDivision a 2 from {
        quotient := c
        remainder := 1
        div_eqv := ‹a ≃ 2 * c + 1›
        rem_mag := ‹abs (1:ℤ) < abs 2›
        rem_sgn := ‹(1:ℤ) * 2 ≥ 0›
      }

    have (And.intro _ (_ : (1:ℤ) ≃ 0)) := flooredDiv_unique odd_div even_div
    show False from absurd ‹(1:ℤ) ≃ 0› one_neqv_zero

  show AA.ExactlyOneOfTwo₁ (Even a) (Odd a) from {
    atLeastOne := ‹Either (Even a) (Odd a)›
    atMostOne := ‹¬(Even a ∧ Odd a)›
  }

/-- Only even integers have even squares. -/
def even_from_sqr_even {a : ℤ} : Even (a^2) → Even a := by
  intro (_ : Even (a^2))
  show Even a

  let even_xor_odd : AA.ExactlyOneOfTwo₁ (Even a) (Odd a) := parity a
  match even_xor_odd.atLeastOne with
  | .inl (_ : Even a) =>
    exact ‹Even a›
  | .inr (_ : Odd a) =>
    have : Odd (a^2) :=
      have a_odd : { b : ℤ // a ≃ 2 * b + 1 } := odd_to_witness ‹Odd a›
      let b := a_odd.val
      have : a ≃ 2 * b + 1 := a_odd.property

      let b' := 2 * b^2 + 2 * b
      have : a^2 ≃ 2 * b' + 1 := calc
        _ = a^2                           := rfl
        _ ≃ (2*b + 1)^2                   := by srw [‹a ≃ 2 * b + 1›]
        _ ≃ (2*b)^2 + 2 * (2*b) * 1 + 1^2 := binom_sqr
        _ ≃ (2*b)^2 + 2 * (2*b) + 1^2     := by srw [mul_identR]
        _ ≃ (2*b)^2 + 2 * (2*b) + 1       := by srw [Natural.pow_absorbL]
        _ ≃ 2^2 * b^2 + 2 * (2*b) + 1     := by srw [Natural.pow_distribR_mul]
        _ ≃ 2 * 2*b^2 + 2 * (2*b) + 1     := by srw [Natural.pow_two]
        _ ≃ 2 * (2*b^2) + 2 * (2*b) + 1   := by srw [AA.assoc]
        _ ≃ 2 * (2*b^2 + 2*b) + 1         := by srw [←mul_distribL]
        _ = 2 * b' + 1                    := rfl
      show Odd (a^2) from odd_from_witness ‹a^2 ≃ 2 * b' + 1›

    have : Even a :=
      have : Even (a^2) ∧ Odd (a^2) := And.intro ‹Even (a^2)› ‹Odd (a^2)›
      let even_xor_odd_sqr : AA.ExactlyOneOfTwo₁ (Even (a^2)) (Odd (a^2)) :=
        parity (a^2)
      have : False := even_xor_odd_sqr.atMostOne ‹Even (a^2) ∧ Odd (a^2)›
      show Even a from ‹False›.elim
    exact ‹Even a›

end Lean4Axiomatic.Integer
