import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*}

variable [GroupWithZero G₀] [Group G] [MulDistribMulAction G₀ G] {S T : Subgroup G} {a : G₀}

theorem smul_mem_pointwise_smul_iff₀ (ha : a ≠ 0) (S : Subgroup G) (x : G) :
    a • x ∈ a • S ↔ x ∈ S := smul_mem_smul_set_iff₀ ha (S : Set G) x

