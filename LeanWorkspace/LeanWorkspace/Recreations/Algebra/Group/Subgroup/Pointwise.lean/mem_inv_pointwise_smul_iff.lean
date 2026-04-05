import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

variable [Group α] [MulDistribMulAction α G]

theorem mem_inv_pointwise_smul_iff {a : α} {S : Subgroup G} {x : G} : x ∈ a⁻¹ • S ↔ a • x ∈ S := mem_inv_smul_set_iff

