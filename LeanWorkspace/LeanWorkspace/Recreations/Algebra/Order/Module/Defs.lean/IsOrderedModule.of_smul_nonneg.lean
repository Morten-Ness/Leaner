import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Ring α] [AddCommGroup β] [Module α β] [PartialOrder α] [PartialOrder β]

theorem IsOrderedModule.of_smul_nonneg [IsOrderedAddMonoid α] [IsOrderedAddMonoid β]
    (h : ∀ a : α, 0 ≤ a → ∀ b : β, 0 ≤ b → 0 ≤ a • b) : IsOrderedModule α β where
  toPosSMulMono := .of_smul_nonneg h
  smul_le_smul_of_nonneg_right _b hb a₁ a₂ := by
    simpa [sub_nonneg, sub_smul] using (h (a₂ - a₁) · _ hb)

