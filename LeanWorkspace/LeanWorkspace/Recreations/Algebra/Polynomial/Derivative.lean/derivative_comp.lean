import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommSemiring R]

theorem derivative_comp (p q : R[X]) :
    Polynomial.derivative (p.comp q) = Polynomial.derivative q * p.derivative.comp q := by
  induction p using Polynomial.induction_on'
  · simp [*, mul_add]
  · simp only [Polynomial.derivative_pow, Polynomial.derivative_mul, monomial_comp, Polynomial.derivative_monomial, Polynomial.derivative_C,
      zero_mul, C_eq_natCast, zero_add, map_mul]
    ring

