import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_mul_C (p : R[X]) (n : ℕ) (a : R) : coeff (p * Polynomial.C a) n = coeff p n * a := by
  rcases p with ⟨p⟩
  simp_rw [← monomial_zero_left, ← ofFinsupp_single, ← ofFinsupp_mul, coeff]
  exact AddMonoidAlgebra.mul_single_zero_apply p a n

