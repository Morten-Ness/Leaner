import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem X_pow_comp {k : ℕ} : (Polynomial.X ^ k).comp p = p ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ, Polynomial.mul_X_comp, ih]

