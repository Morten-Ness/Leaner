import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*}

variable [GroupWithZero G₀] [Group G] [MulDistribMulAction G₀ G] {S T : Subgroup G} {a : G₀}

theorem mem_pointwise_smul_iff_inv_smul_mem₀ (ha : a ≠ 0) (S : Subgroup G) (x : G) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S := mem_smul_set_iff_inv_smul_mem₀ ha (S : Set G) x

