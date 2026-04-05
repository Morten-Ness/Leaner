import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_fin_one (A : Matrix (Fin 1) (Fin 1) α) : Matrix.adjugate A = 1 := Matrix.adjugate_subsingleton A

