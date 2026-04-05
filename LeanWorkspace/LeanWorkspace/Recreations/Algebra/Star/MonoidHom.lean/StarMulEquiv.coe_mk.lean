import Mathlib

variable {F A B C D : Type*}

variable [Mul A] [Mul B] [Mul C] [Mul D]

variable [Star A] [Star B] [Star C] [Star D]

theorem coe_mk (e h₁) : ⇑(⟨e, h₁⟩ : A ≃⋆* B) = e := rfl

