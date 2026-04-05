import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*}

variable [Group G] [AddGroup A] [DistribMulAction G A] {S T : AddSubgroup A} {a : G} {x : A}

theorem mem_inv_pointwise_smul_iff : x ∈ a⁻¹ • S ↔ a • x ∈ S := mem_inv_smul_set_iff

