import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G} {s t : Set α}

theorem stabilizer_mul_self (s : Set G) : (stabilizer G s : Set G) * s = s := by
  ext
  refine ⟨?_, fun h ↦ ⟨_, (stabilizer G s).one_mem, _, h, one_mul _⟩⟩
  rintro ⟨a, ha, b, hb, rfl⟩
  rw [← mem_stabilizer_iff.1 ha]
  exact smul_mem_smul_set hb

