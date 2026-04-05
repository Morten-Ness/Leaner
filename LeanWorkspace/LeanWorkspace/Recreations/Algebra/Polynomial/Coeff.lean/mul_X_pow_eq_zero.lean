import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem mul_X_pow_eq_zero {p : R[X]} {n : ℕ} (H : p * Polynomial.X ^ n = 0) : p = 0 := ext fun k => (Polynomial.coeff_mul_X_pow p n k).symm.trans <| ext_iff.1 H (k + n)

