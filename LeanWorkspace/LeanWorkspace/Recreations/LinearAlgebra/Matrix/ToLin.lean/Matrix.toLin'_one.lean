import Mathlib

variable {R : Type*} [CommSemiring R]

variable {k l m n : Type*} [DecidableEq n] [Fintype n]

theorem Matrix.toLin'_one : Matrix.toLin' (1 : Matrix n n R) = LinearMap.id := Matrix.mulVecLin_one

