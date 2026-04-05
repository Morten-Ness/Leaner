import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Semiring α] [AddCommGroup β] [Module α β]

theorem PosSMulMono.of_smul_nonneg [PartialOrder α] [PartialOrder β] [IsOrderedAddMonoid β]
    (h : ∀ a : α, 0 ≤ a → ∀ b : β, 0 ≤ b → 0 ≤ a • b) : PosSMulMono α β where
  smul_le_smul_of_nonneg_left _a ha b₁ b₂ := by simpa [sub_nonneg, smul_sub] using h _ ha (b₂ - b₁)

