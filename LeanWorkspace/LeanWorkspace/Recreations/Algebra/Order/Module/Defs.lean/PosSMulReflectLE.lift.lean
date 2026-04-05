import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable {γ : Type*} [Preorder α] [Preorder β] [Preorder γ]
  [SMul α β] [SMul α γ] (f : β → γ)

variable [Zero α]

theorem PosSMulReflectLE.lift [PosSMulReflectLE α γ]
    (hf : ∀ {b₁ b₂}, f b₁ ≤ f b₂ ↔ b₁ ≤ b₂)
    (smul : ∀ (a : α) b, f (a • b) = a • f b) : PosSMulReflectLE α β where
  le_of_smul_le_smul_left a ha b₁ b₂ h := hf.1 <| le_of_smul_le_smul_left (by simpa only [smul] using hf.2 h) ha

