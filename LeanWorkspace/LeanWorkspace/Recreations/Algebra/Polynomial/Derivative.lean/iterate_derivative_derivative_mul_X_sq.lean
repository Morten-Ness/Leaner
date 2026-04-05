import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommSemiring R]

theorem iterate_derivative_derivative_mul_X_sq {n : ℕ} (p : R[X]) :
    Polynomial.derivative^[n] (Polynomial.derivative^[2] p * Polynomial.X ^ 2) =
      (Polynomial.derivative^[n + 2] p) * Polynomial.X ^ 2 + (2 * n) • (Polynomial.derivative^[n + 1] p) * Polynomial.X +
        (n * (n - 1)) • Polynomial.derivative^[n] p := by
  convert Polynomial.iterate_derivative_mul_X_pow (Polynomial.derivative^[2] p) n 2
  rcases n with rfl | n; · simp
  rcases n with rfl | n; · simp [sum_range_succ, ← mul_assoc]
  suffices ((n + 1 + 1) * (n + 1) / 2) * 2 = (n + 1 + 1) * (n + 1) by
    simp -implicitDefEqProofs [this, -nsmul_eq_mul, sum_range_succ, Nat.choose_two_right]
    ring
  rw [mul_comm (n + 1 + 1)]
  exact Nat.div_mul_cancel (Nat.two_dvd_mul_add_one _)

