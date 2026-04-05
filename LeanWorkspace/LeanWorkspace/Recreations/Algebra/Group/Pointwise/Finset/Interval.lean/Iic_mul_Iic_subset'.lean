import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [Mul α] [Preorder α] [DecidableEq α]

variable [MulLeftMono α] [MulRightMono α]

theorem Iic_mul_Iic_subset' [LocallyFiniteOrderBot α] (a b : α) : Iic a * Iic b ⊆ Iic (a * b) := Finset.coe_subset.mp <| by simpa using Set.Iic_mul_Iic_subset' _ _

