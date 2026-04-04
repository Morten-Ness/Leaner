import Mathlib

variable {k : Type*} {V : Type*} {P : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable (k) in

theorem coplanar_of_finrank_eq_two (s : Set P) (h : finrank k V = 2) : Coplanar k s := by
  have : FiniteDimensional k V := .of_finrank_eq_succ h
  rw [coplanar_iff_finrank_le_two, ← h]
  exact Submodule.finrank_le _

