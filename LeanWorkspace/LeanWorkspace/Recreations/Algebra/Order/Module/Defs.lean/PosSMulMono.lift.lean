import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable {γ : Type*} [Preorder α] [Preorder β] [Preorder γ]
  [SMul α β] [SMul α γ] (f : β → γ)

variable [Zero α]

theorem PosSMulMono.lift [PosSMulMono α γ]
    (hf : ∀ {b₁ b₂}, f b₁ ≤ f b₂ ↔ b₁ ≤ b₂)
    (smul : ∀ (a : α) b, f (a • b) = a • f b) : PosSMulMono α β where
  smul_le_smul_of_nonneg_left a ha b₁ b₂ hb := by
    simp only [← hf, smul] at *; exact smul_le_smul_of_nonneg_left hb ha

