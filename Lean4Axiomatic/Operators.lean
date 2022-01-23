namespace Operators

class TildeDash (α : Sort u) (β : Sort v) where
  tildeDash : α → α → β

infix:50 " ≃ " => TildeDash.tildeDash

def tildeDashNot {α : Sort u} [TildeDash α Prop] (x y : α) : Prop :=
  ¬ (x ≃ y)

infix:50 " ≄ " => tildeDashNot

end Operators
