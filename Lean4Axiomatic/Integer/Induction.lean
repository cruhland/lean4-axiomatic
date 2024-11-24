import Lean4Axiomatic.Function
import Lean4Axiomatic.Integer.Subtraction

/-!
# Integer induction

We don't usually think of integers as obeying an induction principle like the
natural numbers. But if we consider induction from the viewpoint of type
theory, another definition is what's called the _dependent eliminator_ for a
type. That's a function which, given a family of types `motive : ℤ → Sort u`,
and some important assumptions, gives back a function `(a : ℤ) → motive a`,
showing that there's an inhabitant of the family for every integer. This can be
used to prove properties which hold for all integers, or define functions that
take integers as inputs.

The reason why this is useful is the "important assumptions" piece. For
integers, that means the existence of a function
`(n m : ℕ) → motive ((n:ℤ) - (m:ℤ))` that behaves in a "reasonable" way.
Integer induction says that if you can define such a function, showing `motive`
is inhabited for all inputs of the form `(n:ℤ) - (m:ℤ)`, then you've done all
the work needed to show `motive` is inhabited for all integers. Put another
way, it says that all integers can be expressed in the form `n - m` for some
natural numbers `n` and `m`. This is quite helpful as it's often simpler to
show a result holds for natural numbers than for integers.
-/

namespace Lean4Axiomatic.Integer

open Function (IndexedFamily fsubst)
open Relation.Equivalence (EqvOp)

/-! ## Axioms -/

/--
Class providing the definitions needed for "difference induction" to work on
integers, for a specific motive function.

If you want to apply difference induction, you'll need an instance. To create
an instance, use the functions `ind_ctx_prop` or `ind_ctx_const`.

Once you have an instance, you can then call an induction function in  the
`Induction.Context` namespace: `ind_diff`, `ind_diff_eval`, or
`ind_diff_subst`. Or one of the corresponding recursion helpers: `rec_diff`,
`rec_diff_eval`, or `rec_diff_subst`.

**Important parameters**
- `motive`: The indexed family of Sorts to generate via induction or recursion.
  Facts about integers can be proven with a `ℤ → Prop` motive, while data can
  be generated for each integer with a `ℤ → Type` motive.
- `IndexedFamily motive`: Ensures that `motive` is actually an indexed family
  with respect to equivalence, and provides several useful functions/theorems.
-/
class Induction.Context
    {ℕ : outParam Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    (motive : ℤ → Sort u) [IndexedFamily motive]
    :=
  /--
  The motive holds for every integer of the form `n - m`, where `n` and `m` are
  natural numbers.

  **Intuition**: It turns out that _all_ integers can be placed in that form,
  and this is the benefit of the inductive approach: show that the `motive`
  property holds on a difference of natural numbers, and obtain the result that
  it holds on all integers.
  -/
  on_diff (n m : ℕ) : motive (n - m)

  /--
  The `on_diff` function respects equivalence of natural number differences.

  **Intuition**: For `on_diff` to be a function on integers, and not just pairs
  of natural numbers, it must ensure that differences which represent the same
  integer are considered equivalent by returning equivalent results for them.

  Note that the `fsubst` function must be used to rewrite the type
  `motive (n₁ - m₁)` into the type `motive (n₂ - m₂)` so the output equivalence
  is well-typed.
  -/
  on_diff_subst
    {n₁ m₁ n₂ m₂ : ℕ} {diff_eqv : (n₁:ℤ) - m₁ ≃ n₂ - m₂}
    : fsubst diff_eqv (on_diff n₁ m₁) ≃ on_diff n₂ m₂

/-- Operations pertaining to eliminators on integers. -/
class Induction.Ops
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type) [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    :=
  /--
  Induction principle for integers: if a property holds for all differences of
  two natural numbers, then it holds for all integers.

  The "holds for all differences of natural numbers" part is provided by the
  `Context motive` argument.

  **Intuition**: This can be a bit tough to describe informally without
  circular reasoning. But if we take as our starting point the grade school
  definition of integers as the union of the positive natural numbers, zero,
  and the negations of the positive naturals, then we can see that any
  difference `n - m` where `n m : ℕ` can always be rewritten as either
  `k - 0 ≃ k` or `0 - k ≃ -k`, depending on which of `n` or `m` is greater.

  Ultimately, this operation is asserting that all integers can be
  _represented_ as the difference of two natural numbers.
  -/
  ind_diff
    {motive : ℤ → Sort u} [IndexedFamily motive] (ctx : Context motive) (a : ℤ)
    : motive a

/--
Induction principle for integers: if a property holds for all differences of
two natural numbers, then it holds for all integers.

The "holds for all differences of natural numbers" part is provided by the
`Context motive` argument.

This definition is syntax sugar; it allows a call to
`Integer.Induction.Ops.ind_diff ctx`, or `Integer.ind_diff ctx`, to be written
as the more convenient `ctx.ind_diff` instead.

See `Integer.Induction.Ops.ind_diff` for intuition.
-/
def Induction.Context.ind_diff
    {ℕ : Type} [Natural ℕ]
    {ℤ : Type} [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    [Ops ℤ] {motive : ℤ → Sort u} [IndexedFamily motive]
    : (ctx : Context motive) → (a : ℤ) → motive a
    :=
  Ops.ind_diff

/-- Properties of integer eliminators. -/
class Induction.Props
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type) [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    [Ops ℤ]
    :=
  /--
  The computational behavior of integer induction: when evaluated on a
  difference of two natural numbers, the result is given by applying the
  context's `on_diff` function to those same numbers.

  **Intuition**: Integer induction can somehow treat any integer as a
  difference of natural numbers, so if it's given an integer that's _already
  in that form_, then it must be the case that it uses `on_diff` to process the
  natural numbers directly. This is the intended _meaning_ of `ind_diff` and
  `on_diff`.
  -/
  ind_diff_eval
    {motive : ℤ → Sort u} [IndexedFamily motive] (ctx : Context motive)
    {n m : ℕ}
    : ctx.ind_diff (n - m) ≃ ctx.on_diff n m

  /--
  Integer induction obeys the substitution property on equivalence.

  **Intuition**: Integers are only distinct up to equivalence (not equality),
  so this property is required for integer induction to be a well-behaved
  function.
  -/
  ind_diff_subst
    {motive : ℤ → Sort u} [IndexedFamily motive] {ctx : Context motive}
    {a₁ a₂ : ℤ} {a_eqv : a₁ ≃ a₂}
    : fsubst ‹a₁ ≃ a₂› (ctx.ind_diff a₁) ≃ ctx.ind_diff a₂

/-- All integer induction/eliminator axioms. -/
class Induction
    {ℕ : outParam Type} [Natural ℕ]
    (ℤ : Type) [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ]
    :=
  toOps : Induction.Ops ℤ
  toProps : Induction.Props ℤ

attribute [instance] Induction.toOps
attribute [instance] Induction.toProps

/-! ## Derived properties -/

variable
  {ℕ : Type} [Natural ℕ]
  {ℤ : Type}
    [Core (ℕ := ℕ) ℤ] [Addition ℤ] [Negation ℤ] [Subtraction ℤ] [Induction ℤ]

/--
Convenience constructor of integer induction contexts for `ℤ → Prop` motives.

**Intuition**: All that's needed is a plain `on_diff` function; substitution
always holds because `motive (n₁ - m₁) : Prop` implies
`motive (n₂ - m₂) : Prop` when `n₁ - m₁ ≃ n₂ - m₂`, thus
`on_diff n₁ m₁` and `on_diff n₂ m₂` both have type `motive (n₂ - m₂)` and
therefore are equivalent by proof irrelevance of `Prop` elements.
-/
def ind_ctx_prop
    {motive : ℤ → Prop} [IndexedFamily motive]
    (on_diff : (n m : ℕ) → motive (n - m))
    : Induction.Context motive
    := {
  on_diff := on_diff
  on_diff_subst := Rel.refl
}

/--
Convenience constructor of integer induction contexts for constant motives;
i.e. motives of the form `ℤ → X` where `X` is a single type.

**Intuition**: This allows for the `on_diff` function to be inferred.
-/
def ind_ctx_const
    {X : Sort u} [EqvOp X] {on_diff : ℕ → ℕ → X}
    (on_diff_subst :
      {n₁ m₁ n₂ m₂ : ℕ} → (n₁:ℤ) - m₁ ≃ n₂ - m₂ →
      on_diff n₁ m₁ ≃ on_diff n₂ m₂)
    : Induction.Context (λ (_ : ℤ) => X)
    := {
  on_diff := on_diff
  on_diff_subst := λ {_} {_} {_} {_} {diff_eqv} => on_diff_subst diff_eqv
}

/--
The computational behavior of integer induction: when evaluated on a difference
of two natural numbers, the result is given by applying the context's `on_diff`
function to those same numbers.

This definition is syntax sugar; it allows a call to
`Integer.Induction.Props.ind_diff_eval ctx`, or `Integer.ind_diff_eval ctx`, to
be written as the more convenient `ctx.ind_diff_eval` instead.

See `Integer.Induction.Props.ind_diff_eval` for intuition.
-/
def Induction.Context.ind_diff_eval
    {motive : ℤ → Sort u} [IndexedFamily motive]
    : (ctx : Context motive) → {n m : ℕ} →
      ctx.ind_diff (n - m) ≃ ctx.on_diff n m
    :=
  Induction.Props.ind_diff_eval

/--
Integer induction obeys the substitution property on equivalence.

This definition is syntax sugar; it allows a call to
`Integer.Induction.Props.ind_diff_subst ctx`, or `Integer.ind_diff_subst ctx`,
to be written as the more convenient `ctx.ind_diff_subst` instead.

See `Integer.Induction.Props.ind_diff_subst` for intuition.
-/
def Induction.Context.ind_diff_subst
    {motive : ℤ → Sort u} [IndexedFamily motive]
    (ctx : Context motive) {a₁ a₂ : ℤ} (a_eqv : a₁ ≃ a₂)
    : fsubst ‹a₁ ≃ a₂› (ctx.ind_diff a₁) ≃ ctx.ind_diff a₂
    :=
  Induction.Props.ind_diff_subst

/--
Recursion principle for integers: if a value of some type `X` can be computed
for all differences of two natural numbers, then it can be computed for all
integers.

The "can be computed for all differences of natural numbers" part is provided
by the `Context (λ (_ : ℤ) => X)` argument.

**Intuition**: This is a special case of `ind_diff` when the `motive` returns
the same type for all inputs.
-/
def Induction.Context.rec_diff
    {X : Sort u} [EqvOp X] (ctx : Context (λ (_ : ℤ) => X))
    : ℤ → X
    :=
  ctx.ind_diff

/--
The computational behavior of integer recursion: when evaluated on a difference
of two natural numbers, the result is given by applying the context's `on_diff`
function to those same numbers.

**Intuition**: This is a special case of `ind_diff_eval` when the `motive`
returns the same type for all inputs.
-/
def Induction.Context.rec_diff_eval
    {X : Sort u} [EqvOp X] (ctx : Context (λ (_ : ℤ) => X))
    : {n m : ℕ} → ctx.rec_diff (n - m) ≃ ctx.on_diff n m
    :=
  ctx.ind_diff_eval

/--
Integer recursion obeys the substitution property on equivalence.

**Intuition**: This is a special case of `ind_diff_subst` when the `motive`
returns the same type for all inputs.
-/
def Induction.Context.rec_diff_subst
    {X : Sort u} [EqvOp X] (ctx : Context (λ (_ : ℤ) => X))
    : {a₁ a₂ : ℤ} → (a_eqv : a₁ ≃ a₂) → ctx.rec_diff a₁ ≃ ctx.rec_diff a₂
    :=
  ctx.ind_diff_subst

/--
Every integer can be expressed as a difference of natural numbers.

**Property intution**: See the comment the top of this file, or the intuition
for `ind_diff`.

**Proof intuition**: Use "difference" induction: show the property respects
integer equivalence, define an `on_diff` function, and create a context. Then
use the context to invoke `ind_diff` on the input integer.
-/
theorem as_diff (a : ℤ) : ∃ (n m : ℕ), a ≃ n - m := by
  let motive (z : ℤ) : Prop := ∃ (n m : ℕ), z ≃ n - m

  let msubst {x₁ x₂ : ℤ} : x₁ ≃ x₂ → motive x₁ → motive x₂ := by
    intro (_ : x₁ ≃ x₂) (_ : motive x₁)
    show motive x₂

    have Exists.intro (n : ℕ) (Exists.intro (m : ℕ) (_ : x₁ ≃ n - m)) :=
      ‹motive x₁›
    have : x₂ ≃ n - m := calc
      _ = x₂    := rfl
      _ ≃ x₁    := Rel.symm ‹x₁ ≃ x₂›
      _ ≃ n - m := ‹x₁ ≃ n - m›
    have : ∃ (n m : ℕ), x₂ ≃ n - m := Exists.intro n (Exists.intro m this)
    have : motive x₂ := this
    exact this
  let idx_fam := Function.idx_fam_prop msubst

  let on_diff (k j : ℕ) : motive ((k:ℤ) - j) :=
    Exists.intro k (Exists.intro j Rel.refl)
  let ctx := ind_ctx_prop on_diff

  have : motive a := ctx.ind_diff a
  have : ∃ (n m : ℕ), a ≃ n - m := this
  exact this

end Lean4Axiomatic.Integer
