import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} [Inv α]

theorem iUnion_inv (s : ι → Set α) : (⋃ i, s i)⁻¹ = ⋃ i, (s i)⁻¹ := preimage_iUnion

