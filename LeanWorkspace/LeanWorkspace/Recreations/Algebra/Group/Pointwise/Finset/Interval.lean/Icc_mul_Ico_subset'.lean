import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [Mul α] [PartialOrder α] [DecidableEq α]

variable [MulLeftStrictMono α] [MulRightStrictMono α]

theorem Icc_mul_Ico_subset' [LocallyFiniteOrder α] (a b c d : α) :
    Icc a b * Ico c d ⊆ Ico (a * c) (b * d) := Finset.coe_subset.mp <| by simpa using Set.Icc_mul_Ico_subset' _ _ _ _

