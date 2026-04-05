import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [Mul α] [PartialOrder α] [DecidableEq α]

variable [MulLeftStrictMono α] [MulRightStrictMono α]

theorem Ici_mul_Ioi_subset' [LocallyFiniteOrderTop α] (a b : α) : Ici a * Ioi b ⊆ Ioi (a * b) := Finset.coe_subset.mp <| by simpa using Set.Ici_mul_Ioi_subset' _ _

