import Lean4Axiomatic.Integer.Impl.Difference.Core

namespace Lean4Axiomatic.Integer.Impl.Difference

/-! ## Addition of formal differences -/

variable {ℕ : Type} [Natural ℕ]

/--
Addition of differences.

**Definition intuition**: the sum of two differences should be the net effect
of applying both of them.
-/
def add : Difference ℕ → Difference ℕ → Difference ℕ
| a——b, c——d => (a + c)——(b + d)

instance addOp : Add (Difference ℕ) := {
  add := add
}

/--
Addition of natural number differences is commutative.

**Proof intuition**: Expand definitions to see that we need to show the
equivalence of two differences of natural number sums. The left and right
elements of the differences are directly equivalent via commutativity of
natural number addition, so convert the differences into ordered pairs and use
commutativity element-wise.
-/
theorem add_comm {a b : Difference ℕ} : a + b ≃ b + a := by
  revert a; intro (a₁——a₂); revert b; intro (b₁——b₂)
  show a₁——a₂ + b₁——b₂ ≃ b₁——b₂ + a₁——a₂
  show (a₁ + b₁)——(a₂ + b₂) ≃ (b₁ + a₁)——(b₂ + a₂)
  show from_prod (a₁ + b₁, a₂ + b₂) ≃ from_prod (b₁ + a₁, b₂ + a₂)
  apply AA.subst₁
  show (a₁ + b₁, a₂ + b₂) ≃ (b₁ + a₁, b₂ + a₂)
  calc
    (a₁ + b₁, a₂ + b₂) ≃ _ := AA.substL Natural.add_comm
    (b₁ + a₁, a₂ + b₂) ≃ _ := AA.substR Natural.add_comm
    (b₁ + a₁, b₂ + a₂) ≃ _ := Rel.refl

instance add_commutative : AA.Commutative (α := Difference ℕ) (· + ·) := {
  comm := add_comm
}

/--
Adding the same difference on the right of two equivalent differences preserves
their equivalence.

**Proof intuition**: The property is already intuitively true; imagine
extending two line segments of the same length by the same amount. So the proof
just expands all definitions into equalities of sums of natural numbers, and
performs algebra to obtain the desired result.
-/
theorem add_substL {a₁ a₂ b : Difference ℕ} : a₁ ≃ a₂ → a₁ + b ≃ a₂ + b := by
  revert a₁; intro (n——m); revert a₂; intro (k——j); revert b; intro (p——q)
  intro (_ : n——m ≃ k——j)
  have : n + j ≃ k + m := ‹n——m ≃ k——j›
  show n——m + p——q ≃ k——j + p——q
  show (n + p)——(m + q) ≃ (k + p)——(j + q)
  show (n + p) + (j + q) ≃ (k + p) + (m + q)
  calc
    (n + p) + (j + q) ≃ _ := AA.expr_xxfxxff_lr_swap_rl (f := (· + ·))
    (n + j) + (p + q) ≃ _ := Natural.add_substL ‹n + j ≃ k + m›
    (k + m) + (p + q) ≃ _ := AA.expr_xxfxxff_lr_swap_rl (f := (· + ·))
    (k + p) + (m + q) ≃ _ := Rel.refl

def add_substitutiveL
    : AA.SubstitutiveOn Hand.L (α := Difference ℕ) (· + ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  subst₂ := λ (_ : True) => add_substL
}

instance add_substitutive
    : AA.Substitutive₂ (α := Difference ℕ) (· + ·) AA.tc (· ≃ ·) (· ≃ ·)
    := {
  substitutiveL := add_substitutiveL
  substitutiveR := AA.substR_from_substL_swap (rS := (· ≃ ·)) add_substitutiveL
}

/--
Addition of natural number differences is associative.

**Proof intuition**: Expand definitions to see that we need to show the
equivalence of two differences of natural number sums. The left and right
elements of the differences are directly equivalent via associativity of
natural number addition, so convert the differences into ordered pairs and use
associativity element-wise.
-/
def add_assoc {a b c : Difference ℕ} : (a + b) + c ≃ a + (b + c) := by
  revert a; intro (n——m); revert b; intro (k——j); revert c; intro (p——q)
  show (n——m + k——j) + p——q ≃ n——m + (k——j + p——q)
  show (n + k)——(m + j) + p——q ≃ n——m + (k + p)——(j + q)
  show ((n + k) + p)——((m + j) + q) ≃ (n + (k + p))——(m + (j + q))
  show from_prod ((n + k) + p, (m + j) + q)
     ≃ from_prod (n + (k + p), m + (j + q))
  apply AA.subst₁
  show ((n + k) + p, (m + j) + q) ≃ (n + (k + p), m + (j + q))
  calc
    ((n + k) + p, (m + j) + q) ≃ _ := AA.substL Natural.add_assoc
    (n + (k + p), (m + j) + q) ≃ _ := AA.substR Natural.add_assoc
    (n + (k + p), m + (j + q)) ≃ _ := Rel.refl

def add_associative : AA.Associative (α := Difference ℕ) (· + ·) := {
  assoc := add_assoc
}

/--
The natural number difference `0` is a left additive identity element.

**Property intuition**: Adding nothing to a value should leave it unchanged.

**Proof intuition**: Both components of the literal `0` are also `0`, so we can
use the additive identity property on natural numbers elementwise.
-/
theorem add_identL {a : Difference ℕ} : 0 + a ≃ a := by
  revert a; intro (n——m)
  show 0——0 + n——m ≃ n——m
  show (0 + n)——(0 + m) ≃ n——m
  show from_prod (0 + n, 0 + m) ≃ from_prod (n, m)
  apply AA.subst₁
  show (0 + n, 0 + m) ≃ (n, m)
  calc
    (0 + n, 0 + m) ≃ _ := AA.substL Natural.zero_add
    (n, 0 + m)     ≃ _ := AA.substR Natural.zero_add
    (n, m)         ≃ _ := Rel.refl

def add_identityL : AA.IdentityOn Hand.L (α := Difference ℕ) 0 (· + ·) := {
  ident := add_identL
}

instance add_identity : AA.Identity (α := Difference ℕ) 0 (· + ·) := {
  identityL := add_identityL
  identityR := AA.identityR_from_identityL add_identityL
}

/--
Conversion from `ℕ` to `Difference ℕ` is compatible with addition.

**Proprty intuition**: One would hope this is true, otherwise we could not say
that the set of differences (integers) is a superset of the natural numbers.

**Proof intuition**: Expanding definitions is enough to get us nearly there --
just need to clean up an extra zero.
-/
theorem add_compat_natural
    {n m : ℕ} : (↑(n + m) : Difference ℕ) ≃ ↑n + ↑m
    := by
  show (n + m)——0 ≃ n——0 + m——0
  show (n + m)——0 ≃ (n + m)——(0 + 0)
  show (n + m) + (0 + 0) ≃ (n + m) + 0
  exact Natural.add_substR Natural.add_zero

def add_compatible_from_natural
    : AA.Compatible₂ (α := ℕ) (β := Difference ℕ) (↑·) (· + ·) (· + ·)
    := {
  compat₂ := add_compat_natural
}

instance addition : Addition (ℕ := ℕ) (Difference ℕ) := {
  addOp := addOp
  add_substitutive := add_substitutive
  add_commutative := add_commutative
  add_associative := add_associative
  add_identity := add_identity
  add_compatible_from_natural := add_compatible_from_natural
}

end Lean4Axiomatic.Integer.Impl.Difference
