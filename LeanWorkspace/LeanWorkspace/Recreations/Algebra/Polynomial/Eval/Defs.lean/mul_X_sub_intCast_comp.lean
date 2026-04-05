import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Ring R] {p q r : R[X]}

theorem mul_X_sub_intCast_comp {n : ℕ} :
    (p * (Polynomial.X - (n : R[X]))).comp q = p.comp q * (q - n) := by
  rw [mul_sub, Polynomial.sub_comp, Polynomial.mul_X_comp, ← Nat.cast_comm, Polynomial.natCast_mul_comp, Nat.cast_comm, mul_sub]

