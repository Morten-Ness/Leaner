import Mathlib

variable {A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B] [Add C] [Mul C] [Star C]

theorem refl_symm : (StarRingEquiv.refl : A ≃⋆+* A).symm = StarRingEquiv.refl := rfl

