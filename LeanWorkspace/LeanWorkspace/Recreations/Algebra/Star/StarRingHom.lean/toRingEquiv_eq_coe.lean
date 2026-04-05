import Mathlib

variable {A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B] [Add C] [Mul C] [Star C]

theorem toRingEquiv_eq_coe (e : A ≃⋆+* B) : e.toRingEquiv = e := rfl

