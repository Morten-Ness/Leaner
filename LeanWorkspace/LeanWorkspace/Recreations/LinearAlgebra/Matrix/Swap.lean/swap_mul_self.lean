import Mathlib

variable {R n m : Type*} [Semiring R] [DecidableEq n]

variable [Fintype n]

theorem swap_mul_self (i j : n) : Matrix.swap R i j * Matrix.swap R i j = 1 := by
  simp only [Matrix.swap]
  rw [← Equiv.swap_inv, Equiv.Perm.inv_def]
  simp [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]

