import Mathlib

variable {α β G M : Type*}

variable [InvolutiveInv G] {a b : G}

theorem leftInverse_inv : LeftInverse (fun a : G ↦ a⁻¹) fun a ↦ a⁻¹ := inv_inv

