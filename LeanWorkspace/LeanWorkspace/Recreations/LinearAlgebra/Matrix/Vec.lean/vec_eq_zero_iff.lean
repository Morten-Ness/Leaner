import Mathlib

theorem vec_eq_zero_iff [Zero R] {A : Matrix m n R} : Matrix.vec A = 0 ↔ A = 0 := Matrix.vec_inj (B := 0)

