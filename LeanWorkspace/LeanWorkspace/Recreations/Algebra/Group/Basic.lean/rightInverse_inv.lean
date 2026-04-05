import Mathlib

variable {α β G M : Type*}

variable [InvolutiveInv G] {a b : G}

theorem rightInverse_inv : RightInverse (fun a : G ↦ a⁻¹) fun a ↦ a⁻¹ := inv_inv

