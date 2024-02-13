import Lean4Axiomatic.Relation.Equivalence.Core

/-! # Indexed families of types -/

namespace Lean4Axiomatic.Function

open Relation.Equivalence (EqvOp)

/--
Indicates that the provided function is an index into a collection of related
Sorts that respects equivalence on both the indexing type and each indexed
Sort.

The equivalence aspect is important when proving properties about the indexed
family, as it allows the use of substitution. For example, indexed families
can be viewed as predicates on the indexing type, which makes them commonly
used for induction proofs.
-/
class IndexedFamily {α : Type} [EqvOp α] (fam : α → Sort u) :=
  /-- Each Sort in the indexed family obeys its own equivalence relation. -/
  fam_eqv {x : α} : EqvOp (fam x)

  /--
  Equivalence of the indexing type in an indexed family is respected.

  In more detail: if we have a value of Sort `fam x₁`, and `x₁` is equivalent
  to `x₂`, then we also have a value of Sort `fam x₂`.

  **Intuition**: This must be the case for equivalence on the indexing type to
  be meaningful.
  -/
  fsubst {x₁ x₂ : α} : x₁ ≃ x₂ → fam x₁ → fam x₂

  /--
  Substituting an indexed family's index with itself does nothing.

  Useful when there's a need to add or remove an `fsubst` in an expression.

  **Intuition**: The `fsubst` function should be implementable for all types.
  The only consistent thing it can do when the index value is the same is leave
  the input term unchanged.
  -/
  fsubst_refl {x : α} {fx : fam x} : fsubst Rel.refl fx ≃ fx

  /--
  Composing two indexed family substitutions is the same as a single
  substitution from the first to the last index value.

  Useful when wanting to remove a nested `fsubst` in an expression.

  **Intutition**: The `fsubst` function does not change the underlying terms
  (elements of the family) in a significant way. Substitution is purely an
  operation on types.
  -/
  fsubst_trans
    {x y z : α} {xy : x ≃ y} {yz : y ≃ z} {fx : fam x}
    : fsubst ‹y ≃ z› (fsubst ‹x ≃ y› fx) ≃
      fsubst (Rel.trans ‹x ≃ y› ‹y ≃ z›) fx

  fsubst_substR
    {x y : α} {xy : x ≃ y} {fx₁ fx₂ : fam x}
    : fx₁ ≃ fx₂ → fsubst ‹x ≃ y› fx₁ ≃ fsubst ‹x ≃ y› fx₂

  fsubst_injectR
    {x y : α} {xy : x ≃ y} {fx₁ fx₂ : fam x}
    : fsubst ‹x ≃ y› fx₁ ≃ fsubst ‹x ≃ y› fx₂ → fx₁ ≃ fx₂

attribute [instance] IndexedFamily.fam_eqv

export IndexedFamily (
  fsubst fsubst_injectR fsubst_refl fsubst_substR fsubst_trans
)

instance idx_fam_const_inst
    {α : Type} [EqvOp α] {X : Sort u} [EqvOp X]
    : IndexedFamily (λ (_ : α) => X)
    := {
  fam_eqv := λ {_} => ‹EqvOp X›
  fsubst := λ _ => id
  fsubst_refl := Rel.refl
  fsubst_trans := Rel.refl
  fsubst_substR := id
  fsubst_injectR := id
}

def idx_fam_prop
    {α : Type} [EqvOp α] {fam : α → Prop}
    (fsubst : {x₁ x₂ : α} → x₁ ≃ x₂ → fam x₁ → fam x₂)
    : IndexedFamily fam
    := {
  fam_eqv := Relation.Equivalence.eqvOp_prop_term
  fsubst := fsubst
  fsubst_refl := rfl
  fsubst_trans := rfl
  fsubst_substR := λ _ => rfl
  fsubst_injectR := λ _ => rfl
}

end Lean4Axiomatic.Function
