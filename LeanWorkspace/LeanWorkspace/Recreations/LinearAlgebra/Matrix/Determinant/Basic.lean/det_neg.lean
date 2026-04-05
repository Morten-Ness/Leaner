import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_neg (A : Matrix n n R) : Matrix.det (-A) = (-1) ^ Fintype.card n * Matrix.det A := by
  rw [← Matrix.det_smul, neg_one_smul]

