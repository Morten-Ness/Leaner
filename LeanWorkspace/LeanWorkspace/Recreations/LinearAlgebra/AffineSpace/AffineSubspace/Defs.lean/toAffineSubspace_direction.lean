import Mathlib

variable {k V : Type*} [Ring k] [AddCommGroup V] [Module k V]

theorem toAffineSubspace_direction (s : Submodule k V) : s.toAffineSubspace.direction = s := by
  ext x; simp [← s.toAffineSubspace.vadd_mem_iff_mem_direction _ s.zero_mem]

