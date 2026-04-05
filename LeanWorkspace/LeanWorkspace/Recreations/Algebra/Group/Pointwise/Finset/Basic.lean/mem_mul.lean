import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
  (f : F) {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem mem_mul {x : α} : x ∈ s * t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := mem_image₂

