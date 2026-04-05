import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

variable [Group α] [MulDistribMulAction α G]

theorem singleton_mul_subgroup {H : Subgroup G} {h : G} (hh : h ∈ H) : {h} * (H : Set G) = H := by
  simp [preimage, mul_mem_cancel_left (inv_mem hh)]

