import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
  (f : F) {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem sup_mul_le {β} [SemilatticeSup β] [OrderBot β] {s t : Finset α} {f : α → β} {a : β} :
    sup (s * t) f ≤ a ↔ ∀ x ∈ s, ∀ y ∈ t, f (x * y) ≤ a := sup_image₂_le

