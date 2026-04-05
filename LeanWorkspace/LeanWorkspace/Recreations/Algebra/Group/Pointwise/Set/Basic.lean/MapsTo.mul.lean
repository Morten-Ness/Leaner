import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

theorem MapsTo.mul [Mul β] {A : Set α} {B₁ B₂ : Set β} {f₁ f₂ : α → β}
    (h₁ : MapsTo f₁ A B₁) (h₂ : MapsTo f₂ A B₂) : MapsTo (f₁ * f₂) A (B₁ * B₂) := fun _ h => Set.mul_mem_mul (h₁ h) (h₂ h)

