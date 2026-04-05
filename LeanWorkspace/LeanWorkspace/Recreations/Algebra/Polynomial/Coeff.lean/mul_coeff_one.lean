import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem mul_coeff_one (p q : R[X]) :
    coeff (p * q) 1 = coeff p 0 * coeff q 1 + coeff p 1 * coeff q 0 := by
  rw [Polynomial.coeff_mul, Nat.antidiagonal_eq_map]
  simp [sum_range_succ]

