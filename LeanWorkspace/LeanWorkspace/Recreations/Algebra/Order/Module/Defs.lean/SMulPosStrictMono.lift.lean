import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable {γ : Type*} [Preorder α] [Preorder β] [Preorder γ]
  [SMul α β] [SMul α γ] (f : β → γ)

variable [Zero β] [Zero γ]

theorem SMulPosStrictMono.lift [SMulPosStrictMono α γ]
    (hf : ∀ {b₁ b₂}, f b₁ ≤ f b₂ ↔ b₁ ≤ b₂)
    (smul : ∀ (a : α) b, f (a • b) = a • f b)
    (zero : f 0 = 0) : SMulPosStrictMono α β where
  smul_lt_smul_of_pos_right b hb a₁ a₂ ha := by
    simp only [← lt_iff_lt_of_le_iff_le' hf hf, zero, smul] at *
    exact smul_lt_smul_of_pos_right ha hb

