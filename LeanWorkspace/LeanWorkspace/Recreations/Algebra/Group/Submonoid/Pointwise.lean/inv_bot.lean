import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable {s t u : Set M}

variable [Group G]

theorem inv_bot : (⊥ : Submonoid G)⁻¹ = ⊥ := SetLike.coe_injective <| (Set.inv_singleton 1).trans <| congr_arg _ inv_one

