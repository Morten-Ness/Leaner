import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [Mul α] [PartialOrder α] [DecidableEq α]

variable [MulLeftStrictMono α] [MulRightStrictMono α]

theorem Iio_mul_Iic_subset' [LocallyFiniteOrderBot α] (a b : α) : Iio a * Iic b ⊆ Iio (a * b) := Finset.coe_subset.mp <| by simpa using Set.Iio_mul_Iic_subset' _ _

