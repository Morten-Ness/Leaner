import Mathlib

variable {R : Type*} [CommSemiring R]

variable {k l m n : Type*}

variable [Fintype n]

theorem Matrix.range_mulVecLin (M : Matrix m n R) :
    LinearMap.range M.mulVecLin = span R (Set.range M.col) := by
  rw [← vecMulLinear_transpose, range_vecMulLinear, row_transpose]

