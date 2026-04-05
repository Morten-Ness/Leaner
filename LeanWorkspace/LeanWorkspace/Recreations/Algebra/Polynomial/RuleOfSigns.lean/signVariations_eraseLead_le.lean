import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] (P : Polynomial R)

theorem signVariations_eraseLead_le : Polynomial.signVariations P.eraseLead ≤ Polynomial.signVariations P := by
  by_cases hpz : P = 0
  · simp [hpz]
  · grind [Polynomial.signVariations_eq_eraseLead_add_ite]

