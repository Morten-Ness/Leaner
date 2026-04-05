import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_mul_X_pow (p : R[X]) (n d : ℕ) :
    coeff (p * Polynomial.X ^ n) (d + n) = coeff p d := by
  rw [Polynomial.coeff_mul, Finset.sum_eq_single (d, n), Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · rintro ⟨i, j⟩ h1 h2
    rw [Polynomial.coeff_X_pow, if_neg, mul_zero]
    grind [mem_antidiagonal]
  · grind [mem_antidiagonal]

