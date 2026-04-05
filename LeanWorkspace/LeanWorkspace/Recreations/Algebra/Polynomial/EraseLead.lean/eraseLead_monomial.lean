import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem eraseLead_monomial (i : ℕ) (r : R) : Polynomial.eraseLead (monomial i r) = 0 := by
  classical
  by_cases hr : r = 0
  · subst r
    simp only [monomial_zero_right, Polynomial.eraseLead_zero]
  · rw [Polynomial.eraseLead, natDegree_monomial, if_neg hr, erase_monomial]

