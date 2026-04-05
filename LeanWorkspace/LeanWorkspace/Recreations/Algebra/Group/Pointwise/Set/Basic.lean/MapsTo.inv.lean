import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

theorem MapsTo.inv [InvolutiveInv β] {A : Set α} {B : Set β} {f : α → β} (h : MapsTo f A B) :
    MapsTo (f⁻¹) A (B⁻¹) := fun _ ha => Set.inv_mem_inv.2 (h ha)

