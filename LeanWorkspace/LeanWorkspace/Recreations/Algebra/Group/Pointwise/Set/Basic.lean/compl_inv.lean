import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} [Inv α] {s t : Set α} {a : α}

theorem compl_inv : sᶜ⁻¹ = s⁻¹ᶜ := preimage_compl

