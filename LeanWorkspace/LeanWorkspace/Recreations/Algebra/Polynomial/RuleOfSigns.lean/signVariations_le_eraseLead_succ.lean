import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] (P : Polynomial R)

theorem signVariations_le_eraseLead_succ : Polynomial.signVariations P ≤ Polynomial.signVariations P.eraseLead + 1 := by
  by_cases hpz : P = 0
  · simp [hpz]
  · grind [Polynomial.signVariations_eq_eraseLead_add_ite]

