import Lean4Axiomatic.Natural.Sign

namespace Lean4Axiomatic
namespace Natural

variable {ℕ : Type}
variable [Core ℕ]

instance sign_base : Sign.Base ℕ where
  Positive (n : ℕ) := n ≄ 0
  positive_defn := Iff.intro id id

end Natural
end Lean4Axiomatic
