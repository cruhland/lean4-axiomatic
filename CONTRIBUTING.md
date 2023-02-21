# Contribution guidelines

Please check with the repository owner before creating any pull requests. Not
all changes will be accepted, so it's best to discuss before doing any work.

## Code conventions

When defining a `class` for a set of "axioms", follow these guidelines:

1. All `Type` parameters must be `outParam`: e.g. `{ℤ : outParam Type}`
1. No instance parameters should be `outParam`
1. When referencing prerequisite classes in instance parameters, use the
   most general class available, e.g. `Addition ℚ` not `Addition.Ops ℚ`.
1. When Lean is unable to resolve metavariables in the class parameters on its
   own and needs hints, provide them at the leftmost possible parameter. For
   example, here are some parameters for a rational number class:
   `(ℚ : Type) [Core ℚ] [Addition ℚ]`. Rationals depend on integers, so Lean
   will usually complain that it can't resolve the metavariable for integers.
   And the error will often show up on the last parameter, `[Addition ℚ]` in
   this case. It could be resolved by updating that to `[Addition (ℤ := ℤ) ℚ]`,
   but to maintain consistency in the code and reduce confusion, it's best to
   put the named argument at the earliest possible place, which would be
   `[Core (ℤ := ℤ) ℚ]`.
