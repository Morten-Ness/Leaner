import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommSemiring R]

theorem iterate_derivative_X_pow_eq_natCast_mul (n k : ℕ) :
    Polynomial.derivative^[k] (Polynomial.X ^ n : R[X]) = ↑(Nat.descFactorial n k : R[X]) * Polynomial.X ^ (n - k) := by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, tsub_zero, Nat.descFactorial_zero, Nat.cast_one, one_mul]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Polynomial.derivative_natCast_mul, Polynomial.derivative_X_pow, C_eq_natCast,
      Nat.descFactorial_succ, Nat.sub_sub, Nat.cast_mul]
    simp [mul_assoc, mul_left_comm]

