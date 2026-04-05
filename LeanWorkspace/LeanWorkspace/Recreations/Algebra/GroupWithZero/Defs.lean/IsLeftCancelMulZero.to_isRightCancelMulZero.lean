import Mathlib

variable {G₀ : Type u} {M₀ : Type*}

variable [CommMagma M₀] [Zero M₀]

theorem IsLeftCancelMulZero.to_isRightCancelMulZero [IsLeftCancelMulZero M₀] :
    IsRightCancelMulZero M₀ where
  mul_right_cancel_of_ne_zero := fun hb _ _ h => mul_left_cancel₀ hb <| (mul_comm _ _).trans (h.trans (mul_comm _ _))

