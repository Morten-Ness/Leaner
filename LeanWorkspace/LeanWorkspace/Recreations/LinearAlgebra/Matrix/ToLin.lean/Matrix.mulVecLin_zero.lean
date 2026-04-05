import Mathlib

variable {R : Type*} [CommSemiring R]

variable {k l m n : Type*}

theorem Matrix.mulVecLin_zero [Fintype n] : Matrix.mulVecLin (0 : Matrix m n R) = 0 := LinearMap.ext zero_mulVec

