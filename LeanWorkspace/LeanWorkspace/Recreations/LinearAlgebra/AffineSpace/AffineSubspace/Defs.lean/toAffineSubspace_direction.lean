import Mathlib

variable {k V : Type*} [Ring k] [AddCommGroup V] [Module k V]

theorem toAffineSubspace_direction (s : Submodule k V) : s.toAffineSubspace.direction = s := by
  ext x; simp [← AffineSubspace.vadd_mem_iff_mem_direction s.toAffineSubspace _ s.zero_mem]

