import Lean4Axiomatic.Relation.Equivalence.Core

namespace Lean4Axiomatic.Relation.Equivalence

class IndexedFamily {α : Type} [EqvOp α] (fam : α → Sort u) :=
  fam_eqv {x : α} : EqvOp (fam x)

  fsubst {x₁ x₂ : α} : x₁ ≃ x₂ → fam x₁ → fam x₂

  fsubst_refl {x : α} {fx : fam x} : fsubst Rel.refl fx ≃ fx

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

end Lean4Axiomatic.Relation.Equivalence
