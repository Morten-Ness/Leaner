import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R] [NoZeroDivisors R]

theorem dvd_derivative_iff {P : R[X]} : P ∣ Polynomial.derivative P ↔ Polynomial.derivative P = 0 where
  mp h := by
    by_cases hP : P = 0
    · simp only [hP, Polynomial.derivative_zero]
    exact eq_zero_of_dvd_of_degree_lt h (Polynomial.degree_derivative_lt hP)
  mpr h := by simp [h]

