import Mathlib

open scoped RightActions

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

theorem snd_sub [Sub R] [Sub M] (x₁ x₂ : tsze R M) : (x₁ - x₂).snd = x₁.snd - x₂.snd := rfl

