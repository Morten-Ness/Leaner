import Mathlib

variable {G : Type*}

variable [InvolutiveInv G]

theorem inv_inv (a : G) : a⁻¹⁻¹ = a := InvolutiveInv.inv_inv _

