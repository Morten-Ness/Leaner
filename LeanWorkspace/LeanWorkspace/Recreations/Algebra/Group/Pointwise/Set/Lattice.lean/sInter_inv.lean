import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} [Inv α]

theorem sInter_inv (S : Set (Set α)) : (⋂₀ S)⁻¹ = ⋂ s ∈ S, s⁻¹ := preimage_sInter

