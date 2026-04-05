import Mathlib

variable {R n m : Type*} [Semiring R] [DecidableEq n]

variable [Fintype n]

theorem swap_mulVec (i j : n) (a : n → R) :
    Matrix.swap R i j *ᵥ a = a ∘ Equiv.swap i j := by
  simp [Matrix.swap, PEquiv.toMatrix_toPEquiv_mulVec]

