import Mathlib

variable {α G M R A S : Type*}

variable [Monoid M] [AddMonoid A]

variable {s t u : Set M}

variable [Group G]

theorem coe_inv (S : Submonoid G) : ↑S⁻¹ = (S : Set G)⁻¹ := rfl

