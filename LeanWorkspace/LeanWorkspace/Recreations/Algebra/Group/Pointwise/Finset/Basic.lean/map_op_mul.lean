import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
  (f : F) {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem map_op_mul (s t : Finset α) :
    (s * t).map opEquiv.toEmbedding = t.map opEquiv.toEmbedding * s.map opEquiv.toEmbedding := by
  simp [map_eq_image, Finset.image_op_mul]

