import Mathlib

variable {G₀ : Type*} [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [MulPosReflectLT G₀]

theorem mulRight₀_symm (a : G₀) (ha : 0 < a) :
    (OrderIso.mulRight₀ a ha).symm = OrderIso.mulRight₀ a⁻¹ (Right.inv_pos.2 ha) := by ext; rfl

