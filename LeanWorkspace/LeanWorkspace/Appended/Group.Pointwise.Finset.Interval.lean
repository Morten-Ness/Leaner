import Mathlib

section

open scoped Pointwise

variable {α : Type*}

variable [Mul α] [Preorder α] [DecidableEq α]

variable [MulLeftMono α] [MulRightMono α]

theorem Icc_mul_Icc_subset' [LocallyFiniteOrder α] (a b c d : α) :
    Icc a b * Icc c d ⊆ Icc (a * c) (b * d) := Finset.coe_subset.mp <| by simpa using Set.Icc_mul_Icc_subset' _ _ _ _

end

section

open scoped Pointwise

variable {α : Type*}

variable [Mul α] [PartialOrder α] [DecidableEq α]

variable [MulLeftStrictMono α] [MulRightStrictMono α]

theorem Icc_mul_Ico_subset' [LocallyFiniteOrder α] (a b c d : α) :
    Icc a b * Ico c d ⊆ Ico (a * c) (b * d) := Finset.coe_subset.mp <| by simpa using Set.Icc_mul_Ico_subset' _ _ _ _

end

section

open scoped Pointwise

variable {α : Type*}

variable [Mul α] [Preorder α] [DecidableEq α]

variable [MulLeftMono α] [MulRightMono α]

theorem Ici_mul_Ici_subset' [LocallyFiniteOrderTop α] (a b : α) : Ici a * Ici b ⊆ Ici (a * b) := Finset.coe_subset.mp <| by simpa using Set.Ici_mul_Ici_subset' _ _

end

section

open scoped Pointwise

variable {α : Type*}

variable [Mul α] [PartialOrder α] [DecidableEq α]

variable [MulLeftStrictMono α] [MulRightStrictMono α]

theorem Ici_mul_Ioi_subset' [LocallyFiniteOrderTop α] (a b : α) : Ici a * Ioi b ⊆ Ioi (a * b) := Finset.coe_subset.mp <| by simpa using Set.Ici_mul_Ioi_subset' _ _

end

section

open scoped Pointwise

variable {α : Type*}

variable [Mul α] [PartialOrder α] [DecidableEq α]

variable [MulLeftStrictMono α] [MulRightStrictMono α]

theorem Ico_mul_Icc_subset' [LocallyFiniteOrder α] (a b c d : α) :
    Ico a b * Icc c d ⊆ Ico (a * c) (b * d) := Finset.coe_subset.mp <| by simpa using Set.Ico_mul_Icc_subset' _ _ _ _

end

section

open scoped Pointwise

variable {α : Type*}

variable [Mul α] [PartialOrder α] [DecidableEq α]

variable [MulLeftStrictMono α] [MulRightStrictMono α]

theorem Ico_mul_Ioc_subset' [LocallyFiniteOrder α] (a b c d : α) :
    Ico a b * Ioc c d ⊆ Ioo (a * c) (b * d) := Finset.coe_subset.mp <| by simpa using Set.Ico_mul_Ioc_subset' _ _ _ _

end

section

open scoped Pointwise

variable {α : Type*}

variable [Mul α] [Preorder α] [DecidableEq α]

variable [MulLeftMono α] [MulRightMono α]

theorem Iic_mul_Iic_subset' [LocallyFiniteOrderBot α] (a b : α) : Iic a * Iic b ⊆ Iic (a * b) := Finset.coe_subset.mp <| by simpa using Set.Iic_mul_Iic_subset' _ _

end

section

open scoped Pointwise

variable {α : Type*}

variable [Mul α] [PartialOrder α] [DecidableEq α]

variable [MulLeftStrictMono α] [MulRightStrictMono α]

theorem Iic_mul_Iio_subset' [LocallyFiniteOrderBot α] (a b : α) : Iic a * Iio b ⊆ Iio (a * b) := Finset.coe_subset.mp <| by simpa using Set.Iic_mul_Iio_subset' _ _

end

section

open scoped Pointwise

variable {α : Type*}

variable [Mul α] [PartialOrder α] [DecidableEq α]

variable [MulLeftStrictMono α] [MulRightStrictMono α]

theorem Iio_mul_Iic_subset' [LocallyFiniteOrderBot α] (a b : α) : Iio a * Iic b ⊆ Iio (a * b) := Finset.coe_subset.mp <| by simpa using Set.Iio_mul_Iic_subset' _ _

end

section

open scoped Pointwise

variable {α : Type*}

variable [Mul α] [PartialOrder α] [DecidableEq α]

variable [MulLeftStrictMono α] [MulRightStrictMono α]

theorem Ioc_mul_Ico_subset' [LocallyFiniteOrder α] (a b c d : α) :
    Ioc a b * Ico c d ⊆ Ioo (a * c) (b * d) := Finset.coe_subset.mp <| by simpa using Set.Ioc_mul_Ico_subset' _ _ _ _

end

section

open scoped Pointwise

variable {α : Type*}

variable [Mul α] [PartialOrder α] [DecidableEq α]

variable [MulLeftStrictMono α] [MulRightStrictMono α]

theorem Ioi_mul_Ici_subset' [LocallyFiniteOrderTop α] (a b : α) : Ioi a * Ici b ⊆ Ioi (a * b) := Finset.coe_subset.mp <| by simpa using Set.Ioi_mul_Ici_subset' _ _

end
