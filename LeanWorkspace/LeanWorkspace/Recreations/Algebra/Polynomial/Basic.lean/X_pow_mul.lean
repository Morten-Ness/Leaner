import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem X_pow_mul {n : ℕ} : Polynomial.X ^ n * p = p * Polynomial.X ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    conv_lhs => rw [pow_succ]
    rw [mul_assoc, Polynomial.X_mul, ← mul_assoc, ih, mul_assoc, ← pow_succ]

