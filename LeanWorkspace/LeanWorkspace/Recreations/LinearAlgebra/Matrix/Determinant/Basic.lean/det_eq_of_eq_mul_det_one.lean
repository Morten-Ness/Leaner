import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_eq_of_eq_mul_det_one {A B : Matrix n n R} (C : Matrix n n R) (hC : Matrix.det C = 1)
    (hA : A = B * C) : Matrix.det A = Matrix.det B := calc
    Matrix.det A = Matrix.det (B * C) := congr_arg _ hA
    _ = Matrix.det B * Matrix.det C := Matrix.det_mul _ _
    _ = Matrix.det B := by rw [hC, mul_one]

