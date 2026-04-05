import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Zero α] [Zero β] [SMulWithZero α β]

variable [Preorder α] [Preorder β]

theorem isOrderedModule_iff_smul_one_mono
    [MulOneClass β] [ZeroLEOneClass β] [PosMulMono β] [MulPosMono β] [IsScalarTower α β β] :
    IsOrderedModule α β ↔ Monotone (fun x : α ↦ x • (1 : β)) where
  mp _ := smul_one_mono _
  mpr := IsOrderedModule.of_smul_one_mono

