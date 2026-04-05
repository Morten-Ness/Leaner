import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_one : Matrix.adjugate (1 : Matrix n n α) = 1 := by
  ext
  simp [Matrix.adjugate_def, Matrix.one_apply, Pi.single_apply, eq_comm]

