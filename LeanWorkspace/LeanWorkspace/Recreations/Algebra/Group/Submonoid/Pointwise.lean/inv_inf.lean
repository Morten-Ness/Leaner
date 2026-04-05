import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable {s t u : Set M}

variable [Group G]

theorem inv_inf (S T : Submonoid G) : (S ⊓ T)⁻¹ = S⁻¹ ⊓ T⁻¹ := SetLike.coe_injective Set.inter_inv

