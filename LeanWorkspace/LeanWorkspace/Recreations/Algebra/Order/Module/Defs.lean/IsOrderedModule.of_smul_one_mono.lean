import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Zero α] [Zero β] [SMulWithZero α β]

variable [Preorder α] [Preorder β]

theorem IsOrderedModule.of_smul_one_mono
    [MulOneClass β] [PosMulMono β] [MulPosMono β] [IsScalarTower α β β]
    (h : Monotone (fun x : α ↦ x • (1 : β))) : IsOrderedModule α β where
  smul_le_smul_of_nonneg_left _ ha _ _ hb := by
    have := mul_le_mul_of_nonneg_left hb (by simpa using h ha)
    simpa
  smul_le_smul_of_nonneg_right _ ha _ _ hb := by
    simpa using mul_le_mul_of_nonneg_right (h hb) ha

