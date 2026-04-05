import Mathlib

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem inv_eq_self_iff_inv_subset : s⁻¹ = s ↔ s⁻¹ ⊆ s := ⟨le_of_eq, fun h => antisymm h <| Set.inv_subset.mp h⟩

