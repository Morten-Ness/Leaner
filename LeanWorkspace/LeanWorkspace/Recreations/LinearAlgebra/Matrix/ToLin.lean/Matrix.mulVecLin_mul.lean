import Mathlib

variable {R : Type*} [CommSemiring R]

variable {k l m n : Type*}

variable [Fintype n]

theorem Matrix.mulVecLin_mul [Fintype m] (M : Matrix l m R) (N : Matrix m n R) :
    Matrix.mulVecLin (M * N) = (Matrix.mulVecLin M).comp (Matrix.mulVecLin N) := LinearMap.ext fun _ ↦ (mulVec_mulVec _ _ _).symm

