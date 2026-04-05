import Mathlib

variable {α G A S : Type*}

theorem smul_coe_set [Group G] [SetLike S G] [SubgroupClass S G] {s : S} {a : G} (ha : a ∈ s) :
    a • (s : Set G) = s := by
  ext; simp [Set.mem_smul_set_iff_inv_smul_mem, mul_mem_cancel_left, ha]

