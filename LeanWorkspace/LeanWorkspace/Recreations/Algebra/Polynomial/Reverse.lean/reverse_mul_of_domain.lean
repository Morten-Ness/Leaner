import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem reverse_mul_of_domain {R : Type*} [Semiring R] [NoZeroDivisors R] (f g : R[X]) :
    Polynomial.reverse (f * g) = Polynomial.reverse f * Polynomial.reverse g := by
  by_cases f0 : f = 0
  · simp only [f0, zero_mul, Polynomial.reverse_zero]
  by_cases g0 : g = 0
  · rw [g0, mul_zero, Polynomial.reverse_zero, mul_zero]
  simp [Polynomial.reverse_mul, *]

