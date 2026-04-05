import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem range_nsmulAddMonoidHom (n : ℕ) : (nsmulAddMonoidHom n).range = zmultiples (n : ℤ) := by
  ext m : 1
  simp [mem_zmultiples_iff, dvd_def]
  grind

