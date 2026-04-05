import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [MulPosReflectLT G₀] {a b c : G₀}

theorem inv_pos : 0 < a⁻¹ ↔ 0 < a := by
  suffices ∀ a : G₀, 0 < a → 0 < a⁻¹ from ⟨fun h ↦ inv_inv a ▸ this _ h, this a⟩
  intro a ha
  apply lt_of_mul_lt_mul_right _ ha.le
  apply lt_of_mul_lt_mul_right _ ha.le
  simpa [ha.ne']

