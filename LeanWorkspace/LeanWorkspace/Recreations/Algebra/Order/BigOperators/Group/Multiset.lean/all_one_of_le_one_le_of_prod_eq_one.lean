import Mathlib

variable {ι α β : Type*}

variable [CommMonoid α] [Preorder α] {s t : Multiset α} {a : α}

theorem all_one_of_le_one_le_of_prod_eq_one {α : Type*} [CommMonoid α]
  [PartialOrder α] [IsOrderedMonoid α] {s : Multiset α} :
    (∀ x ∈ s, (1 : α) ≤ x) → s.prod = 1 → ∀ x ∈ s, x = (1 : α) := Quotient.inductionOn s (by
    simp only [quot_mk_to_coe, prod_coe, mem_coe]
    exact fun l => List.all_one_of_le_one_le_of_prod_eq_one)

