import Mathlib

variable {R : Type*} [CommSemiring R]

variable {k l m n : Type*}

variable [Fintype n]

theorem Matrix.mulVecLin_one [DecidableEq n] :
    Matrix.mulVecLin (1 : Matrix n n R) = LinearMap.id := by
  ext; simp [Matrix.one_apply, Pi.single_apply, eq_comm]

