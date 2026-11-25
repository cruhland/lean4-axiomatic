module
-- Import all files in the project here so that they all get compiled when
-- running `lake build`. Imports are transitive, so only a few statements are
-- actually needed.
public import Lean4Axiomatic.Integer.Impl.Difference
public import Lean4Axiomatic.Natural.Impl.Nat
public import Lean4Axiomatic.Rational.Impl.Fraction

@[expose] public section

def hello := "world"
