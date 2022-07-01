import Lean4Axiomatic.Integer.Negation

namespace Lean4Axiomatic.Integer.Impl.Derived

variable {ℕ : Type}
variable [Natural ℕ]
variable {ℤ : Type}
variable [Equality ℤ]
variable [Conversion ℕ ℤ]
variable [Addition.Base ℕ ℤ]
variable [Multiplication.Base ℕ ℤ]
variable [Negation.Base ℕ ℤ]

/--
Zero is a left absorbing element for multiplication.

**Property intuition**: A sum of zero terms should produce the empty sum, i.e.
the additive identity, which is zero.

**Proof intuition**: The only way to produce zero by itself, given the
properties of integer addition and multiplication, is by adding a value to its
negation. So we somehow need to obtain `0 * a + -(0 * a)` from `0 * a`. We can
easily get `0 * a + (0 * a + -(0 * a))` from the additive identity and inverse
properties. The key is then using associativity, distributivity, and again
additive identity to merge the two instances of `0 * a` into one.
-/
def mul_absorbL {a : ℤ} : 0 * a ≃ 0 := calc
  0 * a                      ≃ _ := Rel.symm AA.identR
  0 * a + 0                  ≃ _ := AA.substR (Rel.symm AA.inverseR)
  0 * a + (0 * a + -(0 * a)) ≃ _ := Rel.symm AA.assoc
  (0 * a + 0 * a) + -(0 * a) ≃ _ := AA.substL (Rel.symm AA.distribR)
  (0 + 0) * a + -(0 * a)     ≃ _ := AA.substL (AA.substL AA.identL)
  0 * a + -(0 * a)           ≃ _ := AA.inverseR
  (0 : ℤ)                    ≃ _ := Rel.refl

def mul_absorbingL : AA.AbsorbingOn Hand.L (α := ℤ) 0 (· * ·) := {
  absorb := mul_absorbL
}

def mul_absorbing : AA.Absorbing (α := ℤ) 0 (· * ·) := {
  absorbingL := mul_absorbingL
  absorbingR := AA.absorbingR_from_absorbingL mul_absorbingL
}

def negation_derived : Negation.Derived ℕ ℤ := {
  mul_absorbing := mul_absorbing
}

end Lean4Axiomatic.Integer.Impl.Derived
