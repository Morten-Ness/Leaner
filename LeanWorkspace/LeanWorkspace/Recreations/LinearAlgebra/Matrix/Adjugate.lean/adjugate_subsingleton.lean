import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_subsingleton [Subsingleton n] (A : Matrix n n α) : Matrix.adjugate A = 1 := by
  ext i j
  simp [Subsingleton.elim i j, Matrix.adjugate_apply, det_eq_elem_of_subsingleton _ i, one_apply]

