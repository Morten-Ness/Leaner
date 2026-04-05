import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [Mul α] [PartialOrder α] [DecidableEq α]

variable [MulLeftStrictMono α] [MulRightStrictMono α]

theorem Ico_mul_Ioc_subset' [LocallyFiniteOrder α] (a b c d : α) :
    Ico a b * Ioc c d ⊆ Ioo (a * c) (b * d) := Finset.coe_subset.mp <| by simpa using Set.Ico_mul_Ioc_subset' _ _ _ _

