import Mathlib

variable {A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B] [Add C] [Mul C] [Star C]

theorem symm_symm (e : A ≃⋆+* B) : e.symm.symm = e := rfl

