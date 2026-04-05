import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*} [Monoid M] [AddMonoid A]

variable [Group G] [DistribMulAction G A] {a : G}

theorem mem_inv_pointwise_smul_iff {S : AddSubmonoid A} {x : A} : x ∈ a⁻¹ • S ↔ a • x ∈ S := mem_inv_smul_set_iff

