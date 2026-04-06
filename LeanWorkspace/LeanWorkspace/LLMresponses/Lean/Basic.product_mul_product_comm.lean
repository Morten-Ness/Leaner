import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
  (f : F) {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

theorem product_mul_product_comm [DecidableEq β] (s₁ s₂ : Finset α) (t₁ t₂ : Finset β) :
    (s₁ ×ˢ t₁) * (s₂ ×ˢ t₂) = (s₁ * s₂) ×ˢ (t₁ * t₂) := by
  ext x
  simp [Finset.mem_mul, and_left_comm, and_assoc, exists_and_left, exists_and_right,
    exists_prop]
