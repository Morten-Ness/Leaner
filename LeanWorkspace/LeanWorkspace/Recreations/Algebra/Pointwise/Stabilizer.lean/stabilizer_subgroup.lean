import Mathlib

open scoped Pointwise

variable {G H α : Type*}

variable [Group G] [Group H] [MulAction G α] {a : G}

theorem stabilizer_subgroup (s : Subgroup G) : stabilizer G (s : Set G) = s := by
  simp_rw [SetLike.ext_iff, MulAction.mem_stabilizer_set]
  refine fun a ↦ ⟨fun h ↦ ?_, fun ha b ↦ s.mul_mem_cancel_left ha⟩
  simpa only [smul_eq_mul, SetLike.mem_coe, mul_one] using (h 1).2 s.one_mem

