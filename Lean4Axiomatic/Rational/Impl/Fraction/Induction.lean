import Lean4Axiomatic.Rational.Impl.Fraction.Sign
import Lean4Axiomatic.Rational.Impl.Fraction.Reciprocation
import Lean4Axiomatic.Rational.Induction

namespace Lean4Axiomatic.Rational.Impl.Fraction

/-! ## Induction/eliminators on formal fractions -/

open Function (IndexedFamily fsubst fsubst_refl fsubst_substR fsubst_trans)
open Logic (AP)
open Signed (Positive sgn)

variable {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]

/--
Converting two integers to fractions and then dividing them is equivalent to
forming a fraction directly from the integers.

**Property intuition**: Making this property true is one of the reasons for
introducing formal fractions to begin with: to have a consistent inverse of
multiplication for integers.

**Proof intuition**: Expanding the defintions of fractions and division, and
then simplifying via algebraic identities, gives the result.
-/
theorem div_eqv_fraction
    {a b : ℤ} [AP (Positive b)] : (a : Fraction ℤ) / b ≃ a//b
    := calc
  (a : Fraction ℤ) / b ≃ _ := eqv_refl
  (a//1) / (b//1)      ≃ _ := eqv_refl
  (a//1) * (b//1)⁻¹    ≃ _ := mul_substR recip_positive
  (a//1) * (1//b)      ≃ _ := eqv_refl
  (a * 1)//(1 * b)     ≃ _ := substN AA.identR
  a//(1 * b)           ≃ _ := substD AA.identL
  a//b                 ≃ _ := eqv_refl

/-- Implementation of rational "ratio" induction for formal fractions. -/
def ind_ratio
    {motive : Fraction ℤ → Sort u} [IndexedFamily motive]
    (ctx : Induction.Context motive)
    : (p : Fraction ℤ) → motive p
    := by
  intro (a//b)
  show motive (a//b)
  have : AP (b ≄ 0) := ‹AP (Positive b)›.map Integer.neqv_zero_from_positive
  have : motive (a / b) := ctx.on_ratio a b
  have : motive (a//b) := fsubst div_eqv_fraction ‹motive (a / b)›
  exact this

local instance ind_ops : Induction.Ops (Fraction ℤ) := {
  ind_ratio := ind_ratio
}

/--
Rational number "ratio" induction on formal fractions respects equivalence.
-/
theorem ind_ratio_subst
    {motive : Fraction ℤ → Sort u} [IndexedFamily motive]
    {ctx : Induction.Context motive} {p₁ p₂ : Fraction ℤ} {p_eqv : p₁ ≃ p₂}
    : fsubst ‹p₁ ≃ p₂› (ctx.ind_ratio p₁) ≃ ctx.ind_ratio p₂
    := by
  revert p₁ p₂; intro (a₁//b₁) (a₂//b₂)
  have : AP (b₁ ≄ 0) := ‹AP (Positive b₁)›.map Integer.neqv_zero_from_positive
  have : AP (b₂ ≄ 0) := ‹AP (Positive b₂)›.map Integer.neqv_zero_from_positive

  let p₁ := a₁//b₁; let p₂ := a₂//b₂
  intro (_ : p₁ ≃ p₂)
  show fsubst ‹p₁ ≃ p₂› (ctx.ind_ratio p₁) ≃ ctx.ind_ratio p₂

  let r₁ := (a₁:Fraction ℤ) / b₁; let r₂ := (a₂:Fraction ℤ) / b₂
  have : r₁ ≃ p₁ := div_eqv_fraction
  have : r₂ ≃ p₂ := div_eqv_fraction
  have : r₁ ≃ p₂ := eqv_trans ‹r₁ ≃ p₁› ‹p₁ ≃ p₂›
  have : r₂ ≃ r₁ := eqv_trans ‹r₂ ≃ p₂› (eqv_symm ‹r₁ ≃ p₂›)

  let or₁ := ctx.on_ratio a₁ b₁; let or₂ := ctx.on_ratio a₂ b₂
  have or_subst : or₁ ≃ fsubst ‹r₂ ≃ r₁› or₂ :=
    Rel.symm (ctx.on_ratio_subst ‹r₂ ≃ r₁›)
  calc
    _ = fsubst ‹p₁ ≃ p₂› (ctx.ind_ratio p₁)        := rfl
    _ = fsubst ‹p₁ ≃ p₂› (fsubst ‹r₁ ≃ p₁› or₁)    := rfl
    _ ≃ fsubst (eqv_trans ‹r₁ ≃ p₁› ‹p₁ ≃ p₂›) or₁ := fsubst_trans
    _ = fsubst ‹r₁ ≃ p₂› or₁                       := rfl
    _ ≃ fsubst ‹r₁ ≃ p₂› (fsubst ‹r₂ ≃ r₁› or₂)    := fsubst_substR or_subst
    _ ≃ fsubst (Rel.trans ‹r₂ ≃ r₁› ‹r₁ ≃ p₂›) or₂ := fsubst_trans
    _ = fsubst ‹r₂ ≃ p₂› or₂                       := rfl
    _ = ctx.ind_ratio p₂                           := rfl

/--
The computational behavior of rational number induction on formal fractions.
-/
theorem ind_ratio_eval
    {motive : Fraction ℤ → Sort u} [IndexedFamily motive]
    (ctx : Induction.Context motive) {a b : ℤ} [AP (b ≄ 0)]
    : ctx.ind_ratio (a / b) ≃ ctx.on_ratio a b
    := by
  -- Abbreviations of expressions to keep lines under the max width
  let Fℤ : Type := Fraction ℤ
  let sb := sgn b; let asb := a * sb; let bsb := b * sb

  -- Nonzero instances for values in denominators
  have : Integer.Nonzero b := Integer.nonzero_iff_neqv_zero.mpr ‹AP (b ≄ 0)›.ev
  have : Positive bsb := Integer.positive_mul_sgn_self ‹Integer.Nonzero b›
  have : AP (Positive bsb) := AP.mk ‹Positive bsb›
  have : AP (bsb ≄ 0) := ‹AP (Positive bsb)›.map Integer.neqv_zero_from_positive
  have : AP ((b:Fℤ) * sb ≄ 0) := ‹AP (bsb ≄ 0)›.map $ mt $ by
    intro (_ : (b:Fℤ) * sb ≃ 0)
    show b * sb ≃ 0
    have : (bsb:Fℤ) ≃ (0:Fℤ) := calc
      _ = (bsb:Fℤ)    := rfl
      _ ≃ (b:Fℤ) * sb := mul_compat_from_integer
      _ ≃ 0           := ‹(b:Fℤ) * sb ≃ 0›
    have : bsb ≃ 0 := from_integer_inject ‹(bsb:Fℤ) ≃ (0:Fℤ)›
    exact this

  -- Abbreviations of equivalences to keep lines under the max width
  have srsf : (asb:Fℤ) / bsb ≃ asb//bsb := div_eqv_fraction
  have sfr : asb//bsb ≃ a / b := calc
    _ = asb//bsb                 := rfl
    _ ≃ asb / bsb                := eqv_symm srsf
    _ = (asb:Fℤ) / (bsb:Fℤ)      := rfl
    _ ≃ ((a:Fℤ) * sb) / (bsb:Fℤ) := div_substL mul_compat_from_integer
    _ ≃ ((a:Fℤ) * sb) / (b * sb) := div_substR mul_compat_from_integer
    _ ≃ a / b                    := div_cancelR_mul
  have rsf : (a:Fℤ) / b ≃ asb//bsb := eqv_symm sfr
  have rsr : (a:Fℤ) / b ≃ asb / bsb := eqv_trans rsf (eqv_symm srsf)
  have or_drop_sgn : ctx.on_ratio asb bsb ≃ fsubst rsr (ctx.on_ratio a b) :=
    Rel.symm (ctx.on_ratio_subst rsr)

  -- Prove via equational reasoning
  have unfold : ctx.ind_ratio (asb//bsb) ≃ fsubst rsf (ctx.on_ratio a b) := calc
    _ = ctx.ind_ratio (asb//bsb)                    := rfl
    _ = fsubst srsf (ctx.on_ratio asb bsb)          := rfl
    _ ≃ fsubst srsf (fsubst rsr (ctx.on_ratio a b)) := fsubst_substR or_drop_sgn
    _ ≃ fsubst rsf (ctx.on_ratio a b)               := fsubst_trans
  calc
    _ = ctx.ind_ratio (a / b)                      := rfl
    _ ≃ fsubst sfr (ctx.ind_ratio (asb//bsb))      := Rel.symm ind_ratio_subst
    _ ≃ fsubst sfr (fsubst rsf (ctx.on_ratio a b)) := fsubst_substR unfold
    _ ≃ fsubst eqv_refl (ctx.on_ratio a b)         := fsubst_trans
    _ ≃ ctx.on_ratio a b                           := fsubst_refl

def ind_props : Induction.Props (Fraction ℤ) := {
  ind_ratio_subst := ind_ratio_subst
  ind_ratio_eval := ind_ratio_eval
}

def induction : Induction (Fraction ℤ) := {
  toOps := ind_ops
  toProps := ind_props
}

end Lean4Axiomatic.Rational.Impl.Fraction
