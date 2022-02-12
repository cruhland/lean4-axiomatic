import Lean4Axiomatic.Natural.Addition

namespace ℕ

class Sign.Base (ℕ : Type) [Core ℕ] where
  Positive (n : ℕ) : Prop := n ≄ 0
  positive_defn {n : ℕ} : Positive n ↔ n ≄ 0

class Sign.Derived (ℕ : Type) [Core ℕ] [Addition.Base ℕ]
    extends Sign.Base ℕ where
  positive_subst : AA.Substitutive Positive (· ≃ ·) (· → ·)
  positive_step {n : ℕ} : Positive n → ∃ m : ℕ, step m ≃ n
  positive_add {n m : ℕ} : Positive n → Positive (n + m)

namespace Sign
export Sign.Base (Positive)
end Sign

export Sign (Positive)

end ℕ
