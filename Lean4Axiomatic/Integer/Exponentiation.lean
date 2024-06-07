import Lean4Axiomatic.Integer.Order

/-!
# Integers: exponentiation to natural numbers

The axioms for exponentiation to natural numbers are provided by
`Natural.Exponentiation`. This file uses those axioms as a base to prove some
derived properties.
-/

namespace Lean4Axiomatic.Integer

open Natural (step)

/-! ## Derived properties for exponentiation to a natural number -/

variable
  {ℕ ℤ : Type} [Natural ℕ] [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Multiplication ℤ]
  [Negation ℤ] [Subtraction ℤ] [Sign ℤ] [Order ℤ]
  [Natural.Exponentiation ℕ ℤ (· * ·)]

/-- TODO -/
theorem sgn_pow {a : ℤ} {n : ℕ} : sgn (a^n) ≃ (sgn a)^n := by
  apply Natural.ind_on n
  case zero =>
    show sgn (a^0) ≃ (sgn a)^0
    calc
      _ = sgn (a^0) := rfl
      _ ≃ sgn (1:ℤ) := sgn_subst Natural.pow_zero
      _ ≃ 1         := sgn_positive.mp one_positive
      _ ≃ (sgn a)^0 := Rel.symm Natural.pow_zero
  case step =>
    intro (n' : ℕ) (ih : sgn (a^n') ≃ (sgn a)^n')
    show sgn (a^(step n')) ≃ (sgn a)^(step n')
    calc
      _ = sgn (a^(step n'))  := rfl
      _ ≃ sgn (a^n' * a)     := sgn_subst Natural.pow_step
      _ ≃ sgn (a^n') * sgn a := sgn_compat_mul
      _ ≃ (sgn a)^n' * sgn a := AA.substL ih
      _ ≃ (sgn a)^(step n')  := Rel.symm Natural.pow_step

/-- TODO -/
theorem pow_preserves_pos {a : ℤ} {n : ℕ} : a > 0 → a^n > 0 := by
  intro (_ : a > 0)
  show a^n > 0
  have : sgn a ≃ 1 := gt_zero_sgn.mp ‹a > 0›
  have : sgn (a^n) ≃ 1 := calc
    _ = sgn (a^n) := rfl
    _ ≃ (sgn a)^n := sgn_pow
    _ ≃ 1^n       := Natural.pow_substL ‹sgn a ≃ 1›
    _ ≃ 1         := Natural.pow_absorbL
  have : a^n > 0 := gt_zero_sgn.mpr ‹sgn (a^n) ≃ 1›
  exact this

/-- TODO -/
theorem pow_preserves_nonneg {a : ℤ} {n : ℕ} : a ≥ 0 → a^n ≥ 0 := sorry

/-- TODO -/
theorem pow_pos_preserves_gt_pos
    {a b : ℤ} {n : ℕ} : n > 0 → b ≥ 0 → a > b → a^n > b^n
    := by
  intro (_ : n > 0) (_ : b ≥ 0) (_ : a > b)
  revert ‹n > 0›
  show n > 0 → a^n > b^n

  apply Natural.ind_on n
  case zero =>
    intro (_ : (0:ℕ) > 0)
    show a^0 > b^0
    have : (0:ℕ) ≯ 0 := Natural.lt_zero
    exact absurd ‹(0:ℕ) > 0› ‹(0:ℕ) ≯ 0›
  case step =>
    intro (n' : ℕ) (ih : n' > 0 → a^n' > b^n') (_ : step n' > 0)
    show a^(step n') > b^(step n')
    have : n' ≃ 0 ∨ n' > 0 := Natural.gt_split ‹step n' > 0›
    match this with
    | Or.inl (_ : n' ≃ 0) =>
      have pow_step_reduce {x : ℤ} : x^(step n') ≃ x := calc
        _ = x^(step n') := rfl
        _ ≃ x^(step 0)  := Natural.pow_substR (AA.subst₁ ‹n' ≃ 0›)
        _ ≃ x^1         := Natural.pow_substR (Rel.symm Natural.literal_step)
        _ ≃ x           := Natural.pow_one
      calc
        _ = a^(step n') := rfl
        _ ≃ a           := pow_step_reduce
        _ > b           := ‹a > b›
        _ ≃ b^(step n') := Rel.symm pow_step_reduce
    | Or.inr (_ : n' > 0) =>
      have : a > 0 := trans ‹a > b› ‹b ≥ 0›
      have : b^n' ≥ 0 := pow_preserves_nonneg ‹b ≥ 0›
      have : sgn (a - b) ≃ 1 := gt_sgn.mp ‹a > b›
      have : a^n' > b^n' := ih ‹n' > 0›
      have : sgn (a^n' - b^n') ≃ 1 := gt_sgn.mp ‹a^n' > b^n'›
      have : sgn (a^n' * a - b^n' * a) ≃ 1 := calc
        _ = sgn (a^n' * a - b^n' * a) := rfl
        _ ≃ sgn ((a^n' - b^n') * a)   := sgn_subst (Rel.symm AA.distribR)
        _ ≃ sgn (a^n' - b^n') * sgn a := sgn_compat_mul
        _ ≃ 1 * sgn a                 := AA.substL ‹sgn (a^n' - b^n') ≃ 1›
        _ ≃ sgn a                     := AA.identL
        _ ≃ 1                         := gt_zero_sgn.mp ‹a > 0›
      have : sgn (b^n' * a - b^n' * b) ≥ 0 := calc
        _ = sgn (b^n' * a - b^n' * b) := rfl
        _ ≃ sgn (b^n' * (a - b))      := sgn_subst (Rel.symm AA.distribL)
        _ ≃ sgn (b^n') * sgn (a - b)  := sgn_compat_mul
        _ ≃ sgn (b^n') * 1            := AA.substR ‹sgn (a - b) ≃ 1›
        _ ≃ sgn (b^n')                := AA.identR
        _ ≥ 0                         := sgn_preserves_ge_zero.mp ‹b^n' ≥ 0›
      calc
        _ = a^(step n') := rfl
        _ ≃ a^n' * a    := Natural.pow_step
        _ > b^n' * a    := gt_sgn.mpr ‹sgn (a^n' * a - b^n' * a) ≃ 1›
        _ ≥ b^n' * b    := sgn_diff_ge_zero.mpr ‹sgn (b^n' * a - b^n' * b) ≥ 0›
        _ ≃ b^(step n') := Rel.symm Natural.pow_step

/-- TODO -/
theorem pow_preserves_ge_nonneg
    {a b : ℤ} {n : ℕ} : b ≥ 0 → a ≥ b → a^n ≥ b^n
    := by
  intro (_ : b ≥ 0) (_ : a ≥ b)
  show a^n ≥ b^n
  have : a > b ∨ b ≃ a := le_iff_lt_or_eqv.mp ‹a ≥ b›
  match this with
  | Or.inl (_ : a > b) =>
    have : n > 0 ∨ n ≃ 0 := Natural.ge_split Natural.ge_zero
    match this with
    | Or.inl (_ : n > 0) =>
      have : a^n > b^n := pow_pos_preserves_gt_pos ‹n > 0› ‹b ≥ 0› ‹a > b›
      have : a^n ≥ b^n := le_iff_lt_or_eqv.mpr (Or.inl ‹a^n > b^n›)
      exact this
    | Or.inr (_ : n ≃ 0) =>
      calc
        _ = a^n := rfl
        _ ≃ a^0 := Natural.pow_substR ‹n ≃ 0›
        _ ≥ 1   := le_iff_lt_or_eqv.mpr (Or.inr (Rel.symm Natural.pow_zero))
        _ ≃ b^0 := Rel.symm Natural.pow_zero
        _ ≃ b^n := Natural.pow_substR (Rel.symm ‹n ≃ 0›)
  | Or.inr (_ : b ≃ a) =>
    have : b^n ≃ a^n := Natural.pow_substL ‹b ≃ a›
    have : a^n ≥ b^n := le_iff_lt_or_eqv.mpr (Or.inr ‹b^n ≃ a^n›)
    exact this

theorem sgn_step {n : ℕ} : sgn (step n : ℤ) ≃ 1 := sorry

theorem sgn_diff_pow
    {a b : ℤ} {n : ℕ}
    : a ≥ 0 → b ≥ 0 → sgn (a^n - b^n) ≃ sgn (a - b) * sgn (n:ℤ)
    := by
  intro (_ : a ≥ 0) (_ : b ≥ 0)
  show sgn (a^n - b^n) ≃ sgn (a - b) * sgn (n:ℤ)
  apply Natural.ind_on n
  case zero =>
    have : sgn (0:ℤ) ≃ 0 := sgn_zero.mp Rel.refl
    calc
      _ = sgn (a^0 - b^0)         := rfl
      _ ≃ sgn (1 - b^0)           := sgn_subst (sub_substL Natural.pow_zero)
      _ ≃ sgn ((1:ℤ) - 1)         := sgn_subst (sub_substR Natural.pow_zero)
      _ ≃ sgn (0:ℤ)               := sgn_subst (zero_diff_iff_eqv.mpr Rel.refl)
      _ ≃ 0                       := ‹sgn (0:ℤ) ≃ 0›
      _ ≃ sgn (a - b) * 0         := Rel.symm AA.absorbR
      _ ≃ sgn (a - b) * sgn (0:ℤ) := AA.substR (Rel.symm ‹sgn (0:ℤ) ≃ 0›)
  case step =>
    intro (m : ℕ) (ih : sgn (a^m - b^m) ≃ sgn (a - b) * sgn (m:ℤ))
    -- m ≃ 0:
    -- sgn (a^1 - b^1) = sgn (a - b) * 1 = sgn (a - b) * sgn (step 0)
    -- m > 0:
    -- ih : sgn (a^m - b^m) ≃ sgn (a - b) * sgn m = sgn (a - b)
    -- sgn (a^m * b - b^m * b)
    -- = sgn (a^m - b^m) * sgn b
    -- = sgn (a - b) * sgn b
    -- sgn (a^m * a - a^m * b) = (sgn a)^m * sgn (a - b) = sgn a * sgn (a - b)
    -- sgn a | sgn b | sgn (a - b) | sgn a * sgn (a - b) | sgn (a - b) * sgn b
    --   0   |   0   |     0       |         0           |           0
    --   0   |   1   |    -1       |         0           |          -1
    --   1   |   0   |     1       |         1           |           0
    --   1   |   1   | sgn (a - b) |    sgn (a - b)      |     sgn (a - b)
    calc
      _ = sgn (a^(step m) - b^(step m)) := rfl
      -- sgn (a^m * a - b^m * b)
      -- sgn (a^m * a - a^m * b) = sgn (a^m) * sgn (a - b) = (sgn a)^m * sgn (a - b)
      -- sgn (a^m * b - b^m * b) = sgn (a^m - b^m) * sgn b = sgn (a - b) * sgn (m:ℤ) * sgn b
      _ ≃ sgn (a - b) := sorry
      _ ≃ sgn (a - b) * 1 := Rel.symm AA.identR
      _ ≃ sgn (a - b) * sgn (step m : ℤ) := AA.substR (Rel.symm sgn_step)

theorem sgn_sum_ordered_pos
    {a b : ℤ}
    : sgn a * sgn b ≥ 0 → sgn a ≥ sgn b → sgn b ≥ 0 →
    sgn (a + b) ≃ sgn a + sgn b - (sgn a) * (sgn b)^2
    := by
  -- THIS IS NOT NEEDED
  -- under all constraints, we must have
  -- (sgn a ≃ 1 ∧ sgn b ≃ 1) ∨ (sgn a ≃ 1 ∧ sgn b ≃ 0) ∨ (sgn a ≃ 0 ∧ sgn b ≃ 0)
  -- probably easiest to have a lemma generate the above cases
  -- then do a match on them and evaluate below
  -- sgn a ≃ 1 ∧ sgn b ≃ 1:
  --   sgn (a + b) ≃ 1 b/c add_preserves_sgn
  --   sgn a + sgn b - (sgn a) * (sgn b)^2
  --   = 1 + 1 - 1 * 1^2
  --   = 2 - 1
  --   = 1 ✓
  -- sgn a ≃ 1 ∧ sgn b ≃ 0:
  --   sgn (a + b) = sgn (a + 0) = sgn a = 1
  --   sgn a + sgn b - (sgn a) * (sgn b)^2
  --   = 1 + 0 - 1 * 0^2
  --   = 1 - 0
  --   = 1 ✓
  -- sgn a ≃ 0 ∧ sgn b ≃ 0:
  --   sgn (a + b) = sgn 0 = 0
  --   sgn a + sgn b - (sgn a) * (sgn b)^2
  --   = 0 + 0 - 0 * 0^2
  --   = 0 - 0
  --   = 0 ✓
  admit

theorem sgn_sum_ordered
    {a b : ℤ}
    : sgn a * sgn b ≥ 0 → sgn a ≥ sgn b →
    sgn (a + b) ≃ sgn a + sgn b - (sgn a) * (sgn b)^2
    := by
  -- THIS IS NOT NEEDED
  -- (sgn a, sgn b) combos considered
  -- (1, 1), (1, 0), (0, 0), (0, -1), (-1, -1)
  -- we have b ≥ 0 or b < 0 → b ≤ 0
  -- if b ≥ 0:
  -- then immediately call sgn_sum_ordered_pos
  -- if b < 0:
  -- then call sgn_sum_ordered_pos where
  -- a := -b, b := -a
  -- sgn (-b) * sgn (-a) = -(sgn b) * -(sgn a) = -(-(sgn b * sgn a)) = sgn a * sgn b ≥ 0
  -- sgn (-b) ≥ sgn (-a) → -sgn b ≥ -sgn a → sgn a ≥ sgn b
  -- sgn (-a) ≥ 0 ↔ -sgn a ≥ 0 ↔ sgn a ≤ 0 ... somehow show this
  -- oops, and then you'll have to reverse the result to match the goal
  admit

theorem sgn_sum
    {a b : ℤ} : a * b ≥ 0 → sgn (a + b) ≃ sgn a + sgn b - (sgn a) * (sgn b)^2
    := by
  intro (_ : a * b ≥ 0)
  show sgn (a + b) ≃ sgn a + sgn b - (sgn a) * (sgn b)^2
  have : a * b > 0 ∨ a * b ≃ 0 := ge_split.mp ‹a * b ≥ 0›
  match this with
  | Or.inl (_ : a * b > 0) =>
    have (And.intro (_ : sgn a ≃ sgn b) (_ : a * b ≄ 0)) :=
      mul_gt_zero_iff_sgn_same.mp ‹a * b > 0›
    admit
  | Or.inr (_ : a * b ≃ 0) =>
    -- make a lemma showing when a ≃ 0, both sides are the same
    -- then use lemma for sgn a case and sgn b case, swapping vars
    admit

end Lean4Axiomatic.Integer

-- n > 0 → q ≥ 0 → p > q → p^n > q^n
-- {p q : ℚ} {n : ℕ} : sgn (p^n - q^n) ≃? sgn (p - q) * sgn n
-- n = 0:
-- sgn (p^0 - q^0) = sgn (1 - 1) = sgn 0 = sgn (p - q) * sgn 0 = sgn (p - q) * sgn n
-- n > 0:
-- p ≃ q:
-- sgn (p^n - q^n) = sgn 0 = sgn (p - p) * sgn n = sgn (p - q) * sgn n
-- p > q:
-- sgn (p^n - q^n) = sgn n = 1 * sgn n = sgn (p - q) * sgn n
-- p < q:
-- sgn (p^n - q^n) = -sgn (q^n - p^n) = -sgn n = 1 * -sgn n = sgn (q - p) * -sgn n
-- = -sgn (p - q) * -sgn n = sgn (p - q) * sgn n
