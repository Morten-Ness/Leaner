import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*}

variable [GroupWithZero G₀] [Group G] [MulDistribMulAction G₀ G] {S T : Subgroup G} {a : G₀}

theorem mem_inv_pointwise_smul_iff₀ (ha : a ≠ 0) (S : Subgroup G) (x : G) :
    x ∈ a⁻¹ • S ↔ a • x ∈ S := mem_inv_smul_set_iff₀ ha (S : Set G) x

