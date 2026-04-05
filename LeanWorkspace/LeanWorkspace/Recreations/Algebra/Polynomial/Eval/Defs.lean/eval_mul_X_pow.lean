import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable {x : R}

theorem eval_mul_X_pow {k : ℕ} : (p * Polynomial.X ^ k).eval x = p.eval x * x ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ, ← mul_assoc, ih]

