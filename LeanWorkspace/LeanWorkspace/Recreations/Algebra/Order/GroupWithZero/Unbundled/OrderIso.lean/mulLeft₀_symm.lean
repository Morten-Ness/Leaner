import Mathlib

variable {G₀ : Type*} [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀]

theorem mulLeft₀_symm (a : G₀) (ha : 0 < a) : (OrderIso.mulLeft₀ a ha).symm = OrderIso.mulLeft₀ a⁻¹ (inv_pos.2 ha) := by
  ext; rfl

