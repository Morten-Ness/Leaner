import Mathlib

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a b x : G₀}

theorem GroupWithZero.mul_right_injective (h : x ≠ 0) :
    Function.Injective fun y => x * y := fun y y' w => by
  simpa only [← mul_assoc, inv_mul_cancel₀ h, one_mul] using congr_arg (fun y => x⁻¹ * y) w

