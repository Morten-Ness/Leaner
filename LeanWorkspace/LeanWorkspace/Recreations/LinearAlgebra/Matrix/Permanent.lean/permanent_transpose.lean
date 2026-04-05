import Mathlib

variable {n : Type*} [DecidableEq n] [Fintype n]

variable {R : Type*} [CommSemiring R]

theorem permanent_transpose (M : Matrix n n R) : Mᵀ.permanent = M.permanent := by
  refine sum_bijective _ inv_involutive.bijective _ _ ?_
  intro σ
  apply Fintype.prod_equiv σ
  simp

