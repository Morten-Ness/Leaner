import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_fin_zero (A : Matrix (Fin 0) (Fin 0) α) : Matrix.adjugate A = 0 := Subsingleton.elim _ _

