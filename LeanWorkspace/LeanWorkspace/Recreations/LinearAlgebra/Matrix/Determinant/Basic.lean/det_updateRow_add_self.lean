import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_updateRow_add_self (A : Matrix n n R) {i j : n} (hij : i ≠ j) :
    Matrix.det (updateRow A i (A i + A j)) = Matrix.det A := by
  simp [Matrix.det_updateRow_add,
    Matrix.det_zero_of_row_eq hij (updateRow_self.trans (updateRow_ne hij.symm).symm)]

