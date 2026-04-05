import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [Mul α] [Preorder α] [DecidableEq α]

variable [MulLeftMono α] [MulRightMono α]

theorem Icc_mul_Icc_subset' [LocallyFiniteOrder α] (a b c d : α) :
    Icc a b * Icc c d ⊆ Icc (a * c) (b * d) := Finset.coe_subset.mp <| by simpa using Set.Icc_mul_Icc_subset' _ _ _ _

