import Mathlib

variable {F α β γ : Type*}

variable [MulOneClass α]

theorem subset_mul_right {s : Set α} (t : Set α) (hs : (1 : α) ∈ s) : t ⊆ s * t := fun x hx =>
  ⟨1, hs, x, hx, one_mul _⟩

