import Mathlib

variable {R : Type*} [CommSemiring R]

variable {k l m n : Type*}

theorem Matrix.mulVecLin_apply [Fintype n] (M : Matrix m n R) (v : n → R) :
    M.mulVecLin v = M *ᵥ v := rfl

