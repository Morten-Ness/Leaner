import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

theorem MapsTo.div [Div β] {A : Set α} {B₁ B₂ : Set β} {f₁ f₂ : α → β}
    (h₁ : MapsTo f₁ A B₁) (h₂ : MapsTo f₂ A B₂) : MapsTo (f₁ / f₂) A (B₁ / B₂) := fun _ ha => Set.div_mem_div (h₁ ha) (h₂ ha)

