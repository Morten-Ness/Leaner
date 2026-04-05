import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommSemiring R]

theorem iterate_derivative_X_pow_eq_C_mul (n k : ℕ) :
    Polynomial.derivative^[k] (Polynomial.X ^ n : R[X]) = Polynomial.C (Nat.descFactorial n k : R) * Polynomial.X ^ (n - k) := by
  rw [Polynomial.iterate_derivative_X_pow_eq_natCast_mul n k, C_eq_natCast]

