import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [Mul α] [PartialOrder α] [DecidableEq α]

variable [MulLeftStrictMono α] [MulRightStrictMono α]

theorem Ioi_mul_Ici_subset' [LocallyFiniteOrderTop α] (a b : α) : Ioi a * Ici b ⊆ Ioi (a * b) := Finset.coe_subset.mp <| by simpa using Set.Ioi_mul_Ici_subset' _ _

