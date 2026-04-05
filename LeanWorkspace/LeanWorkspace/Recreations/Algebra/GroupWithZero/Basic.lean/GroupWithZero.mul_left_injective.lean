import Mathlib

variable {M₀ G₀ : Type*}

variable [GroupWithZero G₀] {a b x : G₀}

theorem GroupWithZero.mul_left_injective (h : x ≠ 0) :
    Function.Injective fun y => y * x := fun y y' w => by
  simpa only [mul_assoc, mul_inv_cancel₀ h, mul_one] using congr_arg (fun y => y * x⁻¹) w

