import Lean4Axiomatic.Natural.Sign

namespace ℕ

variable {ℕ : Type}
variable [Core ℕ]

instance : Sign.Base ℕ where
  positive_defn := Iff.intro id id

end ℕ
