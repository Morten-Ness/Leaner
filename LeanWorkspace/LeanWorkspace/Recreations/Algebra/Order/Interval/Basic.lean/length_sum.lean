import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]

variable (s t : NonemptyInterval α) (a : α)

theorem length_sum (f : ι → NonemptyInterval α) (s : Finset ι) :
    (∑ i ∈ s, f i).length = ∑ i ∈ s, (f i).length := map_sum (⟨⟨NonemptyInterval.length, NonemptyInterval.length_zero⟩, NonemptyInterval.length_add⟩ : NonemptyInterval α →+ α) _ _

