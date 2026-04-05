import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable {s t u : Set M}

variable [Group G]

theorem inv_top : (⊤ : Submonoid G)⁻¹ = ⊤ := SetLike.coe_injective <| Set.inv_univ

