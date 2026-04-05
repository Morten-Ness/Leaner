import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]

variable (s t : Interval α) (a : α)

theorem length_sum_le (f : ι → Interval α) (s : Finset ι) :
    (∑ i ∈ s, f i).length ≤ ∑ i ∈ s, (f i).length := Finset.le_sum_of_subadditive _ Interval.length_zero.le Interval.length_add_le _ _

