import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_transpose (M : Matrix n n R) : Mᵀ.det = M.det := by
  rw [Matrix.det_apply', Matrix.det_apply']
  refine Fintype.sum_bijective _ inv_involutive.bijective _ _ ?_
  intro σ
  rw [sign_inv]
  congr 1
  apply Fintype.prod_equiv σ
  simp

