import Mathlib

variable {α G M : Type*}

variable [CommMonoid M] {s₂ s₁ s : Finset α} {a : α} {g f : α → M}

theorem prod_Ico_add [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    [ExistsAddOfLE α] [LocallyFiniteOrder α]
    (f : α → M) (a b c : α) : (∏ x ∈ Ico a b, f (c + x)) = ∏ x ∈ Ico (a + c) (b + c), f x := by
  convert Finset.prod_Ico_add' f a b c using 2
  rw [add_comm]

