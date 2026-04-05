import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable {s t u : Set M}

variable [Group G]

theorem inv_sup (S T : Submonoid G) : (S ⊔ T)⁻¹ = S⁻¹ ⊔ T⁻¹ := (Submonoid.invOrderIso : Submonoid G ≃o Submonoid G).map_sup S T

