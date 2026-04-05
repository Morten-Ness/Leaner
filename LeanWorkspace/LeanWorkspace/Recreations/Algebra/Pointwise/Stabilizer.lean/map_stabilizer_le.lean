import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G} {s t : Set α}

theorem map_stabilizer_le (f : G →* H) (s : Set G) :
    (stabilizer G s).map f ≤ stabilizer H (f '' s) := by
  rintro a
  simp only [Subgroup.mem_map, mem_stabilizer_iff, forall_exists_index, and_imp]
  rintro a ha rfl
  rw [← image_smul_distrib, ha]

