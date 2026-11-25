module
public import Lean4Axiomatic.Natural

@[expose] public section

namespace Lean4Axiomatic

open Natural (step)
open Relation.Equivalence (EqvOp)

/-! # Sequences -/

/-! ## Axioms / Definitions -/

/-- TODO -/
class UnitDiscrete (α : Type u) [LE α] [LT α] where
  /-- TODO -/
  lt_to_le {x y : α} : x < y → x ≤ y

  /-- TODO -/
  inc : α → α

  /-- TODO -/
  lt_inc {x : α} : x < inc x

  /-- TODO -/
  min_separation {x y : α} : x ≤ y ∨ inc y ≤ x

export UnitDiscrete (inc)

/-- TODO -/
theorem UnitDiscrete.le_inc
    {α : Type u} [LE α] [LT α] [Trans (α := α) (· ≤ ·) (· < ·) (· < ·)]
    [UnitDiscrete α] {x y : α} : x ≤ y → x ≤ inc y
    := by
  intro (_ : x ≤ y)
  show x ≤ inc y

  have : x < inc y := trans ‹x ≤ y› lt_inc
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

variable {ℕ : Type} [Natural ℕ]

/-- TODO -/
instance unit_discrete_nat_inst : UnitDiscrete ℕ :=
  let inc := step
  have lt_to_le {n m : ℕ} : n < m → n ≤ m := Natural.le_split.mpr ∘ .inl
  have lt_inc {n : ℕ} : n < inc n := Natural.lt_step

  have min_separation {n m : ℕ} : n ≤ m ∨ inc m ≤ n :=
    match (Natural.trichotomy n m).atLeastOne with
    | .first (_ : n < m) =>
        have : n ≤ m := Natural.le_split.mpr (.inl ‹n < m›)
        .inl ‹n ≤ m›
    | .second (_ : n ≃ m) =>
        have : n ≤ m := Natural.le_split.mpr (.inr ‹n ≃ m›)
        .inl ‹n ≤ m›
    | .third (_ : n > m) =>
        have : inc m ≤ n := calc
          _ = inc m  := rfl
          _ = step m := rfl
          _ ≤ n      := Natural.lt_step_le.mp ‹m < n›
        .inr ‹inc m ≤ n›

  show UnitDiscrete ℕ from {
    lt_to_le := lt_to_le
    inc := inc
    lt_inc := lt_inc
    min_separation := min_separation
  }

/-- TODO -/
instance nat_zero_seq_getElem_inst
    {α : Type v} [EqvOp α]
    : GetElem
        (coll := Sequence 0 α) (idx := ℕ) (elem := α) (valid := λ _ _ => True)
    := {
  getElem s i _ :=
    have : 0 ≤ i := Natural.ge_zero
    s._at ‹0 ≤ i›
}

/-- Build a sequence by repeatedly applying a function to a starting value. -/
def iterate
    (ℕ : Type) [Natural ℕ] {α : Type} [EqvOp α]
    (init : α) (next : α → α) [AA.Substitutive₁ next (· ≃ ·) (· ≃ ·)]
    : Sequence 0 α
    :=
  let nth {n : ℕ} (p : 0 ≤ n) : α := Natural.rec_on n init next

  have nth_subst
      {n₁ n₂ : ℕ} : n₁ ≃ n₂ →
        have : 0 ≤ n₁ := Natural.ge_zero
        have : 0 ≤ n₂ := Natural.ge_zero
        nth ‹0 ≤ n₁› ≃ nth ‹0 ≤ n₂›
      := by
    intro (_ : n₁ ≃ n₂) (_ : 0 ≤ n₁) (_ : 0 ≤ n₂)
    show nth ‹0 ≤ n₁› ≃ nth ‹0 ≤ n₂›
    calc
      _ = nth ‹0 ≤ n₁›                := rfl
      _ = Natural.rec_on n₁ init next := rfl
      _ ≃ Natural.rec_on n₂ init next := by srw [‹n₁ ≃ n₂›]
      _ = nth ‹0 ≤ n₂›                := rfl

  show Sequence 0 α from {
    _at := nth
    subst := nth_subst
  }

/--
When a sequence is generated by iteration, the starting element is located at
index zero.
-/
theorem iterate_at_zero
    {α : Type} [EqvOp α]
    {init : α} {next : α → α} [AA.Substitutive₁ next (· ≃ ·) (· ≃ ·)]
    : (iterate ℕ init next)[0] ≃ init
    :=
  Natural.rec_on_zero

/--
When a sequence is generated by iteration, applying the iteration function to
an element produces the immediately following element.
-/
theorem iterate_at_step
    {α : Type} [EqvOp α]
    {init : α} {next : α → α} {n : ℕ} [AA.Substitutive₁ next (· ≃ ·) (· ≃ ·)]
    : (iterate ℕ init next)[step n] ≃ next (iterate ℕ init next)[n]
    :=
  Natural.rec_on_step

/--
When a binary property holds between every input to a function and its
associated output, then the sequence generated by iteration of the function is
linked by that property.

This allows an implicit iteration given by a function and a property to be
converted into an explicit iterative sequence.
-/
theorem iterate_chain
    {α : Type} [EqvOp α]
    {P : α → α → Prop} [AA.Substitutive₂ P AA.tc (· ≃ ·) (· → ·)]
    {init : α} {next : α → α} [AA.Substitutive₁ next (· ≃ ·) (· ≃ ·)]
    (P_link : (x : α) → P x (next x))
    : (iterate ℕ init next).linked P
    := by
  intro (n : ℕ) _
  let s := iterate ℕ init next
  let motive x := P s[x] s[step x]
  show motive n

  apply Natural.cases_on
  case zero =>
    show motive 0
    have : P init (next init) := P_link init
    have : P (iterate ℕ init next)[0] (next init) :=
      AA.substLFn (Rel.symm iterate_at_zero) ‹P init (next init)›
    have : P s[0] (next init) := this
    have : P s[0] (next (iterate ℕ init next)[0]) :=
      AA.substRFn (AA.subst₁ (Rel.symm iterate_at_zero)) ‹P s[0] (next init)›
    have : P s[0] (iterate ℕ init next)[step 0] :=
      AA.substRFn (Rel.symm iterate_at_step) this
    have : P s[0] s[step 0] := this
    have : motive 0 := this
    exact this
  case step =>
    intro (m : ℕ)
    show motive (step m)
    have : P s[step m] (next s[step m]) := P_link s[step m]
    have : P s[step m] (next (iterate ℕ init next)[step m]) := this
    have : P s[step m] (iterate ℕ init next)[step (step m)] :=
      AA.substRFn (Rel.symm iterate_at_step) this
    have : P s[step m] s[step (step m)] := this
    have : motive (step m) := this
    exact this

/-- No natural number sequence is in infinite descent. -/
theorem inf_desc_impossible
    {s : Sequence 0 ℕ} : ¬(InfiniteDescent s)
    := by
  intro (_ : InfiniteDescent s)
  have desc_at (n : ℕ) : s[n] > s[step n] := ‹InfiniteDescent s› Natural.ge_zero
  show False

  have : s[0] > s[1] := calc
    _ = s[0]      := rfl
    _ > s[step 0] := desc_at 0
    _ ≃ s[1]      := by srw [←Natural.literal_step]

  have : s[0] ≤ s[1] :=
    have lower_bound_at_index : (k n : ℕ) → s[n] ≥ k := by
      apply Natural.ind
      case zero =>
        intro (n : ℕ)
        show s[n] ≥ 0
        exact Natural.ge_zero
      case step =>
        intro (m : ℕ) (ih : (n : ℕ) → s[n] ≥ m) (n : ℕ)
        show s[n] ≥ step m
        have : s[n] > m := calc
          _ = s[n]      := rfl
          _ > s[step n] := desc_at n
          _ ≥ m         := ih (step n)
        have : s[n] ≥ step m := Natural.lt_step_le.mp ‹s[n] > m›
        exact this
    show s[0] ≤ s[1] from lower_bound_at_index s[0] 1

  have : False := Natural.le_gt_false ‹s[0] ≤ s[1]› ‹s[0] > s[1]›
  exact this

end Lean4Axiomatic.Sequence
