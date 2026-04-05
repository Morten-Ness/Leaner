import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Zero α] [Zero β] [SMulWithZero α β]

variable [PartialOrder α] [Preorder β]

theorem PosSMulMono.of_pos (h₀ : ∀ a : α, 0 < a → ∀ b₁ b₂ : β, b₁ ≤ b₂ → a • b₁ ≤ a • b₂) :
    PosSMulMono α β where
  smul_le_smul_of_nonneg_left a ha b₁ b₂ h := by
    obtain ha | ha := ha.eq_or_lt
    · simp [← ha]
    · exact h₀ _ ha _ _ h

