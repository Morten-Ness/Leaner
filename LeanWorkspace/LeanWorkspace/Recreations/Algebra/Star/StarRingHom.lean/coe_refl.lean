import Mathlib

variable {A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B] [Add C] [Mul C] [Star C]

theorem coe_refl : ⇑(StarRingEquiv.refl : A ≃⋆+* A) = id := rfl

