import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

variable [GroupWithZero G₀] [DistribMulAction G₀ A] {S T : AddSubmonoid A} {a : G₀}

theorem mem_inv_pointwise_smul_iff₀ (ha : a ≠ 0) (S : AddSubmonoid A) (x : A) :
    x ∈ a⁻¹ • S ↔ a • x ∈ S := mem_inv_smul_set_iff₀ ha (S : Set A) x

