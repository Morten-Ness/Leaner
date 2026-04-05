import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

variable [GroupWithZero G₀] [MulDistribMulAction G₀ M] {a : G₀}

theorem mem_inv_pointwise_smul_iff₀ (ha : a ≠ 0) (S : Submonoid M) (x : M) :
    x ∈ a⁻¹ • S ↔ a • x ∈ S := mem_inv_smul_set_iff₀ ha (S : Set M) x

