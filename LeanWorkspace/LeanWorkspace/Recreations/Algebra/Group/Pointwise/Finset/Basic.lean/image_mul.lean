import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
  (f : F) {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem image_mul [DecidableEq β] : (s * t).image (f : α → β) = s.image f * t.image f := image_image₂_distrib <| map_mul f

