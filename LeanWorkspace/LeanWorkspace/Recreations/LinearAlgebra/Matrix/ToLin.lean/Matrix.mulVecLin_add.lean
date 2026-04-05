import Mathlib

variable {R : Type*} [CommSemiring R]

variable {k l m n : Type*}

theorem Matrix.mulVecLin_add [Fintype n] (M N : Matrix m n R) :
    (M + N).mulVecLin = M.mulVecLin + N.mulVecLin := LinearMap.ext fun _ ↦ add_mulVec _ _ _

