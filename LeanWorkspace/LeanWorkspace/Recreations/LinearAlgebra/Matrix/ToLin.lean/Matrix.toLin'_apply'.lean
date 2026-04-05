import Mathlib

variable {R : Type*} [CommSemiring R]

variable {k l m n : Type*} [DecidableEq n] [Fintype n]

theorem Matrix.toLin'_apply' (M : Matrix m n R) : Matrix.toLin' M = M.mulVecLin := rfl

