import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable [Group α] [MulDistribMulAction α M]

theorem mem_inv_pointwise_smul_iff {a : α} {S : Submonoid M} {x : M} : x ∈ a⁻¹ • S ↔ a • x ∈ S := mem_inv_smul_set_iff

