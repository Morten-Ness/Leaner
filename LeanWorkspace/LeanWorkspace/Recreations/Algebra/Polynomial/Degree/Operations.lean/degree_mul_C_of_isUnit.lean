import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem degree_mul_C_of_isUnit (ha : IsUnit a) (p : R[X]) : (p * Polynomial.C a).degree = p.degree := by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  nontriviality R
  rw [Polynomial.degree_mul', degree_C ha.ne_zero]
  · simp
  · simpa [ha.mul_left_eq_zero]

