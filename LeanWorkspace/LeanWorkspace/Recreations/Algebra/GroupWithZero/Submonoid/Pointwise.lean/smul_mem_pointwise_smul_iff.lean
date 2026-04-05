import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

variable [Group G] [DistribMulAction G A] {a : G}

theorem smul_mem_pointwise_smul_iff {S : AddSubmonoid A} {x : A} : a • x ∈ a • S ↔ x ∈ S := smul_mem_smul_set_iff

