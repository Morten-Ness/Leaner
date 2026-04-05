import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_pow (A : Matrix n n α) (k : ℕ) : Matrix.adjugate (A ^ k) = Matrix.adjugate A ^ k := by
  induction k with
  | zero => simp
  | succ k IH => rw [pow_succ', Matrix.adjugate_mul_distrib, IH, pow_succ]

