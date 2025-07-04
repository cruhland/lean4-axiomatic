import Lean4Axiomatic.Natural.Sign
import Lean4Axiomatic.Sign

/-! # Generic implementation of natural number signedness properties -/

namespace Lean4Axiomatic.Natural.Impl.Generic

variable {ℕ : Type} [Core ℕ]

def positivity : Signed.Positivity ℕ := {
  Positive := λ n => n ≄ 0
  positive_defn := Iff.intro id id
}

def sign : Sign ℕ := {
  positivity := positivity
}

end Lean4Axiomatic.Natural.Impl.Generic
