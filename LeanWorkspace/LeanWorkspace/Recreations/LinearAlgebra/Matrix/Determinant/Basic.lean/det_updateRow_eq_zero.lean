import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

variable {M : Matrix n n R} {i j : n}

theorem det_updateRow_eq_zero (h : i ≠ j) :
    (M.updateRow j (M i)).det = 0 := Matrix.det_zero_of_row_eq h (by simp [h])

