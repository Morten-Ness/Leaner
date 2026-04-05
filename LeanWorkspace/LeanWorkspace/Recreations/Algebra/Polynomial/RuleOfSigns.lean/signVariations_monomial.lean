import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] (P : Polynomial R)

theorem signVariations_monomial (d : ℕ) (c : R) : Polynomial.signVariations (monomial d c) = 0 := by
  by_cases hcz : c = 0
  · simp [hcz]
  · simp [hcz, Polynomial.signVariations, coeffList_eraseLead (mt (monomial_eq_zero_iff c d).mp hcz)]

