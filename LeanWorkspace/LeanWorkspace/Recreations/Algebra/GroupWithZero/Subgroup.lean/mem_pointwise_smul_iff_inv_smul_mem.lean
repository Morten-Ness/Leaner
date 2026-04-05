import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*}

variable [Group G] [AddGroup A] [DistribMulAction G A] {S T : AddSubgroup A} {a : G} {x : A}

theorem mem_pointwise_smul_iff_inv_smul_mem : x ∈ a • S ↔ a⁻¹ • x ∈ S := mem_smul_set_iff_inv_smul_mem

