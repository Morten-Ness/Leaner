import Mathlib

variable {G₀ : Type u} {M₀ : Type*}

variable [CommMagma M₀] [Zero M₀]

theorem IsRightCancelMulZero.to_isCancelMulZero [IsRightCancelMulZero M₀] :
    IsCancelMulZero M₀ := { IsRightCancelMulZero.to_isLeftCancelMulZero with }

