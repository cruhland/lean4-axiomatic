import Lean4Axiomatic.Natural

namespace Lean4Axiomatic

/-! # Sequences -/

/-! ## Axioms / Definitions -/

variable {ℕ : Type} [Natural ℕ]

/-- An infinite, ordered collection of the provided `Sort`'s values. -/
def Sequence (α : Sort u) : Sort u :=
  /-
  Using this basic definition until there's a need for a more general one.
  The natural numbers are an infinite, ordered collection; mapping them to
  values of the given `Sort` transfers those properties.
  -/
  ℕ → α

/-- When each value in a sequence is less than the one preceding it. -/
def InfiniteDescent {α : Type u} [LT α] (s : Sequence (ℕ := ℕ) α) : Prop :=
  (n : ℕ) → s n > s (n + 1)

/-! ## Derived properties -/

/-- No natural number sequence is in infinite descent. -/
theorem inf_desc_impossible {s : Sequence ℕ} : ¬InfiniteDescent (ℕ := ℕ) s := by
  intro (_ : InfiniteDescent s)
  show False
  admit

end Lean4Axiomatic
