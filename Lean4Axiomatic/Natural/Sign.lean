import Lean4Axiomatic.Natural.Addition

namespace Lean4Axiomatic
namespace Natural

class Sign.Base (ℕ : Type) [Core ℕ] where
  Positive (n : ℕ) : Prop
  positive_defn {n : ℕ} : Positive n ↔ n ≄ 0

class Sign.Derived (ℕ : Type) [Core ℕ] [Addition.Base ℕ]
    extends Sign.Base ℕ where
  positive_subst : AA.Substitutive Positive (· ≃ ·) (· → ·)
  positive_step {n : ℕ} : Positive n → ∃ m : ℕ, step m ≃ n
  positive_add {n m : ℕ} : Positive n → Positive (n + m)

namespace Sign
export Sign.Base (Positive positive_defn)
export Sign.Derived (positive_step)
end Sign

export Sign (Positive)

end Natural
end Lean4Axiomatic
