import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem Int.zmultiples_one : AddSubgroup.zmultiples (1 : ℤ) = ⊤ := by
  ext z
  simp [Int.mem_zmultiples_iff]

