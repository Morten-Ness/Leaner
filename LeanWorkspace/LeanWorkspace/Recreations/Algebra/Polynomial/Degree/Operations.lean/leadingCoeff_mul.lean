import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R]

variable [NoZeroDivisors R] {p q : R[X]}

theorem leadingCoeff_mul (p q : R[X]) : leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q := by
  by_cases hp : p = 0
  · simp only [hp, zero_mul, leadingCoeff_zero]
  · by_cases hq : q = 0
    · simp only [hq, mul_zero, leadingCoeff_zero]
    · rw [Polynomial.leadingCoeff_mul']
      exact mul_ne_zero (mt leadingCoeff_eq_zero.1 hp) (mt leadingCoeff_eq_zero.1 hq)

