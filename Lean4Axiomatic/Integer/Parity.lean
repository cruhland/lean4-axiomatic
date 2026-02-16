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

export Parity.Props (even_rem odd_rem)

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
    [Natural.Exponentiation ℕ ℤ]

def half_floored (a : ℤ) : ℤ := (div_floored a 2).quotient

/-- Equivalent integers have equivalent floored halves. -/
@[gcongr]
theorem half_floored_subst
    {a₁ a₂ : ℤ} : a₁ ≃ a₂ → half_floored a₁ ≃ half_floored a₂
    := by
  intro (_ : a₁ ≃ a₂)
  show half_floored a₁ ≃ half_floored a₂

  let d₁ := div_floored a₁ 2; let q₁ := d₁.quotient
  let d₂ := div_floored a₂ 2; let q₂ := d₂.quotient
  have : q₁ ≃ q₂ := div_floored_substL_quot ‹a₁ ≃ a₂›
  have : half_floored a₁ ≃ half_floored a₂ := ‹q₁ ≃ q₂›
  exact this

variable [Parity ℤ]

omit [Subtraction ℤ] [Natural.Exponentiation ℕ ℤ] in
theorem odd_eqv {a : ℤ} : Odd a → a ≃ 2 * half_floored a + 1 := by
  intro (_ : Odd a)
  show a ≃ 2 * half_floored a + 1

  let d := div_floored a 2; let q := d.quotient; let r := d.remainder
  calc
    _ = a                      := rfl
    _ ≃ 2 * q + r              := d.div_eqv
    _ = 2 * half_floored a + r := rfl
    _ ≃ 2 * half_floored a + 1 := by srw [odd_rem.mp ‹Odd a›]

-- These are maybe not needed?
def even_to_witness {a : ℤ} : Even a → { b : ℤ // a ≃ 2 * b } := sorry
def odd_to_witness {a : ℤ} : Odd a → { b : ℤ // a ≃ 2 * b + 1 } := sorry

theorem even_eqv {a : ℤ} : Even a → a ≃ 2 * half_floored a := sorry
def even_from_eqv {a b : ℤ} : a ≃ 2 * b → Even a := sorry

/-- Any integer of the form `2 * b + 1` is odd. -/
def odd_from_eqv {a b : ℤ} : a ≃ 2 * b + 1 → Odd a := by
  intro (_ : a ≃ 2 * b + 1)
  show Odd a

  let d₁ := div_floored a 2; let q := d₁.quotient; let r := d₁.remainder
  let d₂ : FlooredDivision a 2 :=
    -- Could use a numeric tactic for these
    have : abs (1:ℤ) < abs 2 := calc
      _ = abs (1:ℤ) := rfl
      _ ≃ 1         := abs_ident one_ge_zero
      _ < 2         := two_gt_one
      _ ≃ abs (2:ℤ) := Rel.symm $ abs_ident two_ge_zero
    have : (1:ℤ) * 2 ≥ 0 := calc
      _ = (1:ℤ) * 2 := rfl
      _ ≃ 2         := AA.identL
      _ ≥ 0         := two_ge_zero
    show FlooredDivision a 2 from {
      quotient := b
      remainder := 1
      div_eqv := ‹a ≃ 2 * b + 1›
      rem_mag := ‹abs (1:ℤ) < abs 2›
      rem_sgn := ‹(1:ℤ) * 2 ≥ 0›
    }
  have (And.intro _ (_ : r ≃ 1)) := flooredDiv_unique d₁ d₂
  have : Odd a := odd_rem.mpr ‹r ≃ 1›
  exact this

/-- Every integer is either even or odd, but not both. -/
def parity (a : ℤ) : AA.ExactlyOneOfTwo₁ (Even a) (Odd a) :=
  let d := div_floored a 2; let q := d.quotient; let r := d.remainder

  have : Either (Even a) (Odd a) :=
    have : Either (r ≃ 0) (r ≃ 1) :=
      have : r * 2 ≥ 0 * 2 := calc
        _ = r * 2 := rfl
        _ ≥ 0     := d.rem_sgn
        _ ≃ 0 * 2 := Rel.symm AA.absorbL
      have : r ≥ 0 := mul_cancelR_le two_gt_zero ‹r * 2 ≥ 0 * 2›
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
            _ ≃ 2     := abs_ident two_ge_zero
          show Either (r ≃ 0) (r ≃ 1) from (lt_ge_false ‹r < 2› ‹r ≥ 2›).elim

    match ‹Either (r ≃ 0) (r ≃ 1)› with
    | .inl (_ : r ≃ 0) =>
      have : Even a := even_rem.mpr ‹r ≃ 0›
      show Either (Even a) (Odd a) from .inl ‹Even a›
    | .inr (_ : r ≃ 1) =>
      have : Odd a := odd_rem.mpr ‹r ≃ 1›
      show Either (Even a) (Odd a) from .inr ‹Odd a›

  have : ¬(Even a ∧ Odd a) := λ (And.intro (_ : Even a) (_ : Odd a)) =>
    have : (1:ℤ) ≃ 0 := calc
      _ = (1:ℤ) := rfl
      _ ≃ r     := Rel.symm (odd_rem.mp ‹Odd a›)
      _ ≃ 0     := even_rem.mp ‹Even a›
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
      let b := half_floored a
      have : a ≃ 2 * b + 1 := odd_eqv ‹Odd a›

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
      show Odd (a^2) from odd_from_eqv ‹a^2 ≃ 2 * b' + 1›

    have : Even a :=
      have : Even (a^2) ∧ Odd (a^2) := And.intro ‹Even (a^2)› ‹Odd (a^2)›
      let even_xor_odd_sqr : AA.ExactlyOneOfTwo₁ (Even (a^2)) (Odd (a^2)) :=
        parity (a^2)
      have : False := even_xor_odd_sqr.atMostOne ‹Even (a^2) ∧ Odd (a^2)›
      show Even a from ‹False›.elim
    exact ‹Even a›

end Lean4Axiomatic.Integer
