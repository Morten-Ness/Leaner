import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_neg_eq_smul (A : Matrix n n R) :
    Matrix.det (-A) = (-1 : Units ℤ) ^ Fintype.card n • Matrix.det A := by
  rw [← Matrix.det_smul_of_tower, Units.neg_smul, one_smul]

