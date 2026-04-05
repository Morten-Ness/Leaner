import Mathlib

variable {n m R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommSemiring R]

variable (s : ℤˣ) (A B : Matrix n n R) (i j : n)

theorem mul_adjp_add_detp : A * Matrix.adjp 1 A + Matrix.detp (-1) A • 1 = A * Matrix.adjp (-1) A + Matrix.detp 1 A • 1 := by
  ext i j
  rcases eq_or_ne i j with rfl | h <;> simp_rw [add_apply, smul_apply, smul_eq_mul]
  · simp_rw [Matrix.mul_adjp_apply_eq, one_apply_eq, mul_one, add_comm]
  · simp_rw [Matrix.mul_adjp_apply_ne A i j h, one_apply_ne h, mul_zero]

