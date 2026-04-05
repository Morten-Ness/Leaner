import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*}

variable [GroupWithZero G₀] [AddGroup A] [DistribMulAction G₀ A] {S T : AddSubgroup A} {a : G₀}

theorem smul_mem_pointwise_smul_iff₀ (ha : a ≠ 0) (S : AddSubgroup A) (x : A) :
    a • x ∈ a • S ↔ x ∈ S := smul_mem_smul_set_iff₀ ha (S : Set A) x

