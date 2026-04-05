import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
  (f : F) {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem union_mul_inter_subset_union : (s₁ ∪ s₂) * (t₁ ∩ t₂) ⊆ s₁ * t₁ ∪ s₂ * t₂ := image₂_union_inter_subset_union

