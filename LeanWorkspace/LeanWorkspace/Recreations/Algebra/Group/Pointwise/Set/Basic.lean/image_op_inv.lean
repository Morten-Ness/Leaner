import Mathlib

variable {F α β γ : Type*}

variable [InvolutiveInv α] {s t : Set α} {a : α}

theorem image_op_inv : op '' s⁻¹ = (op '' s)⁻¹ := by
  simp_rw [← Set.image_inv_eq_inv, Function.Semiconj.set_image op_inv s]

