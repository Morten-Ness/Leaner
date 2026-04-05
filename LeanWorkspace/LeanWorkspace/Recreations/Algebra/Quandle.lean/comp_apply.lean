import Mathlib

variable {S₁ : Type*} {S₂ : Type*} {S₃ : Type*} [Shelf S₁] [Shelf S₂] [Shelf S₃]

theorem comp_apply (g : S₂ →◃ S₃) (f : S₁ →◃ S₂) (x : S₁) : (g.comp f) x = g (f x) := rfl

