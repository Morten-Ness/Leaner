import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

variable [GroupWithZero G₀] [MulDistribMulAction G₀ M] {a : G₀}

theorem mem_pointwise_smul_iff_inv_smul_mem₀ (ha : a ≠ 0) (S : Submonoid M) (x : M) :
    x ∈ a • S ↔ a⁻¹ • x ∈ S := mem_smul_set_iff_inv_smul_mem₀ ha (S : Set M) x

