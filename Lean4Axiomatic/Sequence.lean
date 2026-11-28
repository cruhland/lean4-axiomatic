module
public import Lean4Axiomatic.AbstractAlgebra.Substitutive

@[expose] public section

namespace Lean4Axiomatic

open Lean4Axiomatic.Relation.Equivalence (EqvOp)

/-! # Sequences -/

/-! ## Axioms / Definitions -/

/-- A _unit discrete_ type has the properties needed for indexing a sequence. -/
class UnitDiscrete (α : Type u) [LE α] [LT α] where
  /--
  Ensures the _less than_ relation is compatible with
  _less than or equivalent to_.

  Note: this is only needed until a better ordering typeclass is available, to
  replace `LE` and `LT`.
  -/
  lt_to_le {x y : α} : x < y → x ≤ y

  /--
  Increment: the value "immediately following" the provided value.

  When indexing into a sequence, this enables us to go from one element to the
  next.
  -/
  inc : α → α

  /--
  Increment always produces a larger value.

  Without this requirement, `inc` might stay in place, or move backward.
  -/
  inc_greater {x : α} : x < inc x

  /--
  An increment is the smallest possible gap between values.

  Without this requirement, `inc` might skip over valid indices.
  -/
  inc_minimal {x y : α} : inc x ≤ y ∨ y ≤ x

export UnitDiscrete (inc)

/-- TODO -/
theorem UnitDiscrete.le_inc
    {α : Type u} [LE α] [LT α] [Trans (α := α) (· ≤ ·) (· < ·) (· < ·)]
    [UnitDiscrete α] {x y : α} : x ≤ y → x ≤ inc y
    := by
  intro (_ : x ≤ y)
  show x ≤ inc y

  have : x < inc y := trans ‹x ≤ y› inc_greater
  have : x ≤ inc y := lt_to_le ‹x < inc y›
  exact this

variable
  {ι : Type u}
    [EqvOp ι] [LE ι] [LT ι] [UnitDiscrete ι]
    [Trans (α := ι) (· ≤ ·) (· ≃ ·) (· ≤ ·)]

/-- TODO: An infinite, ordered collection of the provided `Type`'s values. -/
structure Sequence (base : ι) (α : Type v) [EqvOp α] [UnitDiscrete ι] where
  /--
  TODO: The element identified by the provided index value.

  Using this basic definition until there's a need for a more general one. It
  works well because the natural numbers are infinite and ordered, so assigning
  an element to each of them gives us the properties we want for a sequence.
  -/
  _at {idx : ι} : base ≤ idx → α

  /-- TODO: Equivalent index values produce equivalent elements. -/
  subst
    {n₁ n₂ : ι} {p : base ≤ n₁} (idx_eqv : n₁ ≃ n₂)
    : have : base ≤ n₂ := trans ‹base ≤ n₁› ‹n₁ ≃ n₂›
      _at ‹base ≤ n₁› ≃ _at ‹base ≤ n₂›

namespace Sequence

/-- Enable indexing notation for sequences. -/
instance seq_getElem_inst
    {base : ι} {α : Type v} [EqvOp α]
    : GetElem
        (coll := Sequence base α) (idx := ι) (elem := α)
        (valid := λ _ i => base ≤ i)
    := {
  getElem s _ p := s._at p
}

/-! ## Derived properties -/

/--
Equivalent index values produce equivalent elements.

Corollary of `Sequence.subst` that uses indexing syntax, for use with `gcongr`.
-/
@[gcongr]
theorem at_substR
    {base : ι} {α : Type v} [EqvOp α] {s : Sequence base α}
    {n₁ n₂ : ι} {p : base ≤ n₁} (idx_eqv : n₁ ≃ n₂)
    : have : base ≤ n₂ := trans ‹base ≤ n₁› ‹n₁ ≃ n₂›
      s[n₁] ≃ s[n₂]
    := by
  intro (_ : base ≤ n₂)
  show s[n₁] ≃ s[n₂]
  exact s.subst ‹n₁ ≃ n₂›

/-- Apply a function to every element of a sequence. -/
def map
    {base : ι} {α : Type v} {β : Type w} [EqvOp α] [EqvOp β]
    (f : α → β) [AA.Substitutive₁ f (· ≃ ·) (· ≃ ·)]
    (s : Sequence base α) : Sequence base β
    :=
  let map_at {n : ι} (p : base ≤ n) := f s[n]

  have map_at_subst
      {n₁ n₂ : ι} {p : base ≤ n₁} (idx_eqv : n₁ ≃ n₂)
      : have : base ≤ n₂ := trans ‹base ≤ n₁› ‹n₁ ≃ n₂›
        map_at ‹base ≤ n₁› ≃ map_at ‹base ≤ n₂›
      := by
    intro (_ : base ≤ n₂)
    show map_at ‹base ≤ n₁› ≃ map_at ‹base ≤ n₂›

    calc
      _ = map_at ‹base ≤ n₁› := rfl
      _ = f s[n₁]            := rfl
      _ ≃ f s[n₂]            := AA.subst₁ (by srw [‹n₁ ≃ n₂›])
      _ = map_at ‹base ≤ n₂› := rfl

  show Sequence base β from {
    _at := map_at
    subst := map_at_subst
  }

/-- How to compute the element of a mapped sequence at an index. -/
theorem map_index
    {base : ι} {α : Type v} {β : Type w} [EqvOp α] [EqvOp β]
    {f : α → β} [AA.Substitutive₁ f (· ≃ ·) (· ≃ ·)]
    {s : Sequence base α} {n : ι} {p : base ≤ n}
    : (s.map f)[n] ≃ f s[n]
    :=
  Rel.refl

variable [Trans (α := ι) (· ≤ ·) (· < ·) (· < ·)]

/--
A sequence is _linked_ by a property when that property holds between
consecutive elements.
-/
def linked
    {base : ι} {α : Type v} [EqvOp α] (P : α → α → Prop) (s : Sequence base α)
    : Prop
    :=
  {n : ι} → (p : base ≤ n) →
    have : base ≤ inc n := UnitDiscrete.le_inc ‹base ≤ n›
    P s[n] s[inc n]

/-- When each value in a sequence is less than the one preceding it. -/
def InfiniteDescent
    {base : ι} {α : Type v} [EqvOp α] [LT α] (s : Sequence base α) : Prop
    :=
  s.linked (· > ·)

/--
A sequence obeying a chain property that applies a function to both sequence
elements can be re-expressed as: a sequence with the function mapped over it,
obeying a simpler chain property that doesn't include the function.

In other words, a function can be moved between the chain property and the
sequence.
-/
theorem map_chain
    {base : ι} {α : Type v} {β : Type w} [EqvOp α] [EqvOp β]
    {s : Sequence base α}
    {P : β → β → Prop} [AA.Substitutive₂ P AA.tc (· ≃ ·) (· → ·)]
    {f : α → β} [AA.Substitutive₁ f (· ≃ ·) (· ≃ ·)]
    (orig_chain
      : {n : ι} → (p : base ≤ n) →
        have : base ≤ inc n := UnitDiscrete.le_inc ‹base ≤ n›
        P (f s[n]) (f s[inc n]))
    : (s.map f).linked P
    :=
  let chain
      {n : ι} (p : base ≤ n)
      : have : base ≤ inc n := UnitDiscrete.le_inc ‹base ≤ n›
        P (s.map f)[n] (s.map f)[inc n]
      := by
    intro (_ : base ≤ inc n)
    have : P (f s[n]) (f s[inc n]) := orig_chain ‹base ≤ n›
    have : P (s.map f)[n] (f s[inc n]) := AA.substLFn (Rel.symm map_index) this
    have : P (s.map f)[n] (s.map f)[inc n] :=
      AA.substRFn (Rel.symm map_index) this
    exact this
  have : (s.map f).linked P := chain
  this

end Lean4Axiomatic.Sequence
