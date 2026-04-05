import Mathlib

variable {m n : Type*} [Fintype m] [Fintype n]

theorem den_neg (A : Matrix m n ℚ) : (-A).den = A.den := eq_of_forall_dvd <| by simp [Matrix.den_dvd_iff]

