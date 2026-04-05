import Mathlib

variable {G H : Type*}

theorem val_mrange_zero [MulZeroOneClass G] [MulZeroOneClass H] (f : G →*₀ H) :
    ((0 : MonoidHom.mrange f) : H) = 0 := rfl

