import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem mul_X_pow_comp {k : ℕ} : (p * Polynomial.X ^ k).comp r = p.comp r * r ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih, pow_succ, ← mul_assoc, Polynomial.mul_X_comp]

