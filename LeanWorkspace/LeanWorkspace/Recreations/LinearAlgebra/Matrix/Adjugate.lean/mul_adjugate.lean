import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

set_option backward.isDefEq.respectTransparency false in
theorem mul_adjugate (A : Matrix n n α) : A * Matrix.adjugate A = A.det • (1 : Matrix n n α) := by
  ext i j
  rw [mul_apply, Pi.smul_apply, Pi.smul_apply, one_apply, smul_eq_mul, mul_boole]
  simp [Matrix.mul_adjugate_apply, Matrix.sum_cramer_apply, Matrix.cramer_transpose_row_self, Pi.single_apply, eq_comm]

