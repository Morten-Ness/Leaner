import Mathlib

variable {ι m n p : Type*} {α R S : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

theorem trace_vecMulVec [NonUnitalNonAssocSemiring R] (a b : n → R) :
    Matrix.trace (vecMulVec a b) = a ⬝ᵥ b := by
  rw [vecMulVec_eq Unit, Matrix.trace_replicateCol_mul_replicateRow]

