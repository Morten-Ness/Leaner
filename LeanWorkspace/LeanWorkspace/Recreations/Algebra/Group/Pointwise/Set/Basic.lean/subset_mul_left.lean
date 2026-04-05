import Mathlib

variable {F α β γ : Type*}

variable [MulOneClass α]

theorem subset_mul_left (s : Set α) {t : Set α} (ht : (1 : α) ∈ t) : s ⊆ s * t := fun x hx =>
  ⟨x, hx, 1, ht, mul_one _⟩

