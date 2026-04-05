import Mathlib

variable {R n m : Type*} [Semiring R] [DecidableEq n]

variable [Fintype n]

theorem swap_mulVec_apply (i j : n) (a : n → R) :
    (Matrix.swap R i j *ᵥ a) i = a j := by
  simp [Matrix.swap, PEquiv.toMatrix_toPEquiv_mulVec]

