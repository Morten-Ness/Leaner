import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

variable [Group α] [MulDistribMulAction α G]

theorem subgroup_mul_singleton {H : Subgroup G} {h : G} (hh : h ∈ H) : (H : Set G) * {h} = H := by
  simp [preimage, mul_mem_cancel_right (inv_mem hh)]

