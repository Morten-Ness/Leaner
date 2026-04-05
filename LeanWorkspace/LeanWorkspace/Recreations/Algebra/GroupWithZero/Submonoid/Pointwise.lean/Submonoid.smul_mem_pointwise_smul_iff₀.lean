import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

variable [GroupWithZero G₀] [MulDistribMulAction G₀ M] {a : G₀}

theorem smul_mem_pointwise_smul_iff₀ (ha : a ≠ 0) (S : Submonoid M) (x : M) :
    a • x ∈ a • S ↔ x ∈ S := smul_mem_smul_set_iff₀ ha (S : Set M) x

