import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem leadingCoeff_monomial (a : R) (n : ℕ) : Polynomial.leadingCoeff (monomial n a) = a := by
  classical
  by_cases ha : a = 0
  · simp only [ha, (monomial n).map_zero, Polynomial.leadingCoeff_zero]
  · rw [Polynomial.leadingCoeff, Polynomial.natDegree_monomial, if_neg ha, coeff_monomial]
    simp

