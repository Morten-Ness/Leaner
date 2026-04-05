import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommSemiring R]

theorem iterate_derivative_derivative_mul_X {n : ℕ} (p : R[X]) :
    Polynomial.derivative^[n] (Polynomial.derivative p * Polynomial.X) = (Polynomial.derivative^[n + 1] p) * Polynomial.X + n • Polynomial.derivative^[n] p := by
  convert Polynomial.iterate_derivative_mul_X_pow (Polynomial.derivative p) n 1; · simp
  rcases n with rfl | n <;> simp [sum_range_succ]

