import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

variable {M : Matrix n n R} {i j : n}

theorem det_updateCol_eq_zero (h : i ≠ j) :
    (M.updateCol j (fun k ↦ M k i)).det = 0 := Matrix.det_zero_of_column_eq h (by simp [h])

