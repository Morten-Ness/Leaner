import Mathlib

variable {α G A S : Type*}

theorem inv_coe_set [InvolutiveInv G] [SetLike S G] [InvMemClass S G] {H : S} : (H : Set G)⁻¹ = H := Set.ext fun _ => inv_mem_iff

