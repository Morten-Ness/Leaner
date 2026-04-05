import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} [Inv α]

theorem iInter_inv (s : ι → Set α) : (⋂ i, s i)⁻¹ = ⋂ i, (s i)⁻¹ := preimage_iInter

