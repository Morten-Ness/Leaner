import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [InvolutiveInv α] {s : Finset α} {a : α}

theorem preimage_inv (s : Finset α) : s.preimage (·⁻¹) inv_injective.injOn = s⁻¹ := coe_injective <| by rw [coe_preimage, Set.inv_preimage, Finset.coe_inv]

