# lean4-axiomatic

A math library that defines concepts abstractly, allowing for multiple
implementations. Uses Lean 4's `class`es to do this in a composable and
convenient fashion. See [natural numbers](Lean4Axiomatic/Natural.lean),
[integers](Lean4Axiomatic/Integer.lean), and
[rational numbers](Lean4Axiomatic/Rational.lean) for examples.

## Building

1. [Set up Lean 4](https://github.com/leanprover/lean4/blob/master/doc/setup.md#setting-up-lean)
1. Clone this repo
1. Run `lake build` in the repo's root directory.
