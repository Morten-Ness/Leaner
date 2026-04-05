import Mathlib

variable {m n : Type*} [Fintype m] [Fintype n]

theorem den_map_intCast (A : Matrix m n ℤ) : (A.map (↑)).den = 1 := by
  simp [← Nat.dvd_one, Matrix.den_dvd_iff]

