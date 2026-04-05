import Mathlib

variable {α G A S : Type*}

theorem coe_set_eq_one [Group G] {s : Subgroup G} : (s : Set G) = 1 ↔ s = ⊥ := (SetLike.ext'_iff.trans (by rfl)).symm

