import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*}

variable [GroupWithZero G₀] [AddGroup A] [DistribMulAction G₀ A] {S T : AddSubgroup A} {a : G₀}

theorem mem_pointwise_smul_iff_inv_smul_mem₀ (ha : a ≠ 0) (S : AddSubgroup A) (x : A) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S := mem_smul_set_iff_inv_smul_mem₀ ha (S : Set A) x

