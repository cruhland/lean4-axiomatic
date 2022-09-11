
namespace Lean4Axiomatic

/--
Negation of disjunction, one of
[De Morgan's laws](https://en.wikipedia.org/wiki/De_Morgan%27s_laws).
-/
theorem not_or_iff_and_not {p q : Prop} : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  case mp =>
    intro (_ : ¬(p ∨ q))
    show ¬p ∧ ¬q
    have : ¬p := by
      intro (_ : p)
      show False
      have : p ∨ q := Or.inl ‹p›
      exact absurd ‹p ∨ q› ‹¬(p ∨ q)›
    have : ¬q := by
      intro (_ : q)
      show False
      have : p ∨ q := Or.inr ‹q›
      exact absurd ‹p ∨ q› ‹¬(p ∨ q)›
    exact And.intro ‹¬p› ‹¬q›
  case mpr =>
    intro (And.intro (_ : ¬p) (_ : ¬q)) (_ : p ∨ q)
    show False
    match ‹p ∨ q› with
    | Or.inl (_ : p) => exact absurd ‹p› ‹¬p›
    | Or.inr (_ : q) => exact absurd ‹q› ‹¬q›

end Lean4Axiomatic
