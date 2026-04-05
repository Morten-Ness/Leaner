import Mathlib

variable {R n m : Type*} [Semiring R] [DecidableEq n]

variable [Fintype n]

theorem vecMul_swap_apply (i j : n) (a : n → R) :
    (a ᵥ* Matrix.swap R i j) i = a j := by
  simp [Matrix.swap, PEquiv.vecMul_toMatrix_toPEquiv]

