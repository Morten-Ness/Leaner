import Mathlib

variable {G₀ : Type u} {M₀ : Type*}

variable [CommMagma M₀] [Zero M₀]

theorem IsLeftCancelMulZero.to_isCancelMulZero [IsLeftCancelMulZero M₀] :
    IsCancelMulZero M₀ := { IsLeftCancelMulZero.to_isRightCancelMulZero with }

