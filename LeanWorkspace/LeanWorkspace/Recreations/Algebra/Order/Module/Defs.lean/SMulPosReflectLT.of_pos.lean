import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Zero α] [Zero β] [SMulWithZero α β]

variable [Preorder α] [PartialOrder β]

theorem SMulPosReflectLT.of_pos (h₀ : ∀ b : β, 0 < b → ∀ a₁ a₂ : α, a₁ • b < a₂ • b → a₁ < a₂) :
    SMulPosReflectLT α β where
  lt_of_smul_lt_smul_right b hb a₁ a₂ h := by
    obtain hb | hb := hb.eq_or_lt
    · simp [← hb] at h
    · exact h₀ _ hb _ _ h

