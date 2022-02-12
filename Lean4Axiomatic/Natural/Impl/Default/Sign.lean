import Lean4Axiomatic.Natural.Sign

namespace ℕ

variable {ℕ : Type}
variable [Core ℕ]

instance sign_base : Sign.Base ℕ where
  Positive (n : ℕ) := n ≄ 0
  positive_defn := Iff.intro id id

end ℕ
