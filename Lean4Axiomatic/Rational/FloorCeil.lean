import Lean4Axiomatic.Rational.Order

/-! # Rational numbers: floor and ceiling functions -/

namespace Lean4Axiomatic.Rational

/-! ## Axioms -/

/-- Floor and ceiling functions on rational numbers. -/
class FloorCeil.Ops (ℤ : Type) (ℚ : Type) :=
  /-- The greatest integer less than or equivalent to the given value. -/
  floor : ℚ → ℤ

  /-- The least integer greater than or equivalent to the given value. -/
  ceil : ℚ → ℤ

export FloorCeil.Ops (ceil floor)

class FloorCeil.Props
    {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Negation ℚ]
    [Sign ℚ] [Subtraction ℚ] [Order ℚ] [Ops ℤ ℚ]
    :=
  /-- A rational is no smaller than its floor. -/
  floor_ub {p : ℚ} : (floor p : ℤ) ≤ p

  /--
  A rational's floor is the greatest integer not greater than the rational
  itself.
  -/
  floor_lb {p : ℚ} {a : ℤ} : a ≤ p → a ≤ floor p

  /-- A rational is no larger than its ceiling. -/
  ceil_lb {p : ℚ} : p ≤ (ceil p : ℤ)

  /--
  A rational's ceiling is the least integer not less than the rational itself.
  -/
  ceil_ub {p : ℚ} {a : ℤ} : p ≤ a → ceil p ≤ a

export FloorCeil.Props (ceil_lb ceil_ub floor_lb floor_ub)

class FloorCeil
    {ℕ ℤ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
    (ℚ : Type) [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Negation ℚ]
    [Sign ℚ] [Subtraction ℚ] [Order ℚ]
    :=
  toOps : FloorCeil.Ops (ℤ := ℤ) ℚ
  toProps : FloorCeil.Props ℚ

attribute [instance] FloorCeil.toOps
attribute [instance] FloorCeil.toProps

/-! ## Derived properties -/

variable
  {ℕ ℤ ℚ : Type} [Natural ℕ] [Integer (ℕ := ℕ) ℤ]
  [Core (ℤ := ℤ) ℚ] [Addition ℚ] [Multiplication ℚ] [Negation ℚ]
  [Sign ℚ] [Subtraction ℚ] [Order ℚ] [FloorCeil ℚ]

/--
A rational is less than an integer if its floor is.

This is equivalent to the contrapositive of `floor_lb`.
-/
theorem floor_lb_mt {p : ℚ} {a : ℤ} : floor p < a → p < a := by
  intro (_ : floor p < a)
  show p < a
  have : ¬(floor p ≥ a) := Integer.not_ge_iff_lt.mpr ‹floor p < a›
  have : ¬(a ≤ floor p) := ‹¬(floor p ≥ a)›
  -- ↓ begin key steps ↓
  have : ¬(a ≤ p) := mt floor_lb ‹¬(a ≤ floor p)›
  -- ↑  end key steps  ↑
  have : ¬(p ≥ a) := ‹¬(a ≤ p)›
  have : p < a := not_ge_iff_lt.mp ‹¬(p ≥ a)›
  exact this

/-- Every rational number is located between consecutive integers. -/
theorem between_integers {p : ℚ} : ∃ (a : ℤ), a ≤ p ∧ p < a + 1 := by
  have : (floor p : ℤ) ≤ p := floor_ub
  have : (floor p : ℤ) < floor p + 1 := Integer.lt_inc
  have : p < (floor p : ℤ) + 1 := calc
    -- ↓ begin key steps ↓
    _ = p                 := rfl
    _ < (floor p + 1 : ℤ) := floor_lb_mt ‹(floor p : ℤ) < floor p + 1›
    -- ↑  end key steps  ↑
    _ ≃ (floor p : ℤ) + 1 := add_compat_from_integer
  have : ∃ (a : ℤ), a ≤ p ∧ p < a + 1 :=
    -- TODO: Do we need all of these annotations?
    Exists.intro (floor p) (And.intro ‹(floor p : ℤ) ≤ p› ‹p < (floor p : ℤ) + 1›)
  exact this

end Lean4Axiomatic.Rational
