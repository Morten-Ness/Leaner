import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [Mul α] [Preorder α] [DecidableEq α]

variable [MulLeftMono α] [MulRightMono α]

theorem Ici_mul_Ici_subset' [LocallyFiniteOrderTop α] (a b : α) : Ici a * Ici b ⊆ Ici (a * b) := Finset.coe_subset.mp <| by simpa using Set.Ici_mul_Ici_subset' _ _

