import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_units_conj (M : (Matrix m m R)ˣ) (N : Matrix m m R) :
    Matrix.det (M.val * N * M⁻¹.val) = Matrix.det N := by
  rw [Matrix.det_mul_right_comm, Units.mul_inv, one_mul]

-- TODO(https://github.com/leanprover-community/mathlib4/issues/6607): fix elaboration so `val` isn't needed

