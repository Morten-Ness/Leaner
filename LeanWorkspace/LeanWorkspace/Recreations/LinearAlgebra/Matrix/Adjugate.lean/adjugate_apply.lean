import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_apply (A : Matrix n n α) (i j : n) :
    Matrix.adjugate A i j = (A.updateRow j (Pi.single i 1)).det := by
  rw [Matrix.adjugate_def, of_apply, Matrix.cramer_apply, updateCol_transpose, det_transpose]

