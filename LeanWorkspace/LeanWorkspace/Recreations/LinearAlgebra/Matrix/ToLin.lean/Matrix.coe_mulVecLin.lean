import Mathlib

variable {R : Type*} [CommSemiring R]

variable {k l m n : Type*}

theorem Matrix.coe_mulVecLin [Fintype n] (M : Matrix m n R) :
    (M.mulVecLin : _ → _) = M.mulVec := rfl

