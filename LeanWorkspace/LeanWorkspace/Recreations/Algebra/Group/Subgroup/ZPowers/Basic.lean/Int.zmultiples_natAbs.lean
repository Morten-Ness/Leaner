import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem Int.zmultiples_natAbs (a : ℤ) :
    AddSubgroup.zmultiples (a.natAbs : ℤ) = AddSubgroup.zmultiples a := by
  simp [le_antisymm_iff, Int.mem_zmultiples_iff, Int.dvd_natAbs, Int.natAbs_dvd]

