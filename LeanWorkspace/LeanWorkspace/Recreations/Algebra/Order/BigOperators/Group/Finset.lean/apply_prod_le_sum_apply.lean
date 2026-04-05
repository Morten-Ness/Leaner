import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid α] [AddCommMonoid β] [Preorder β] [AddLeftMono β]
  (s : Finset ι) {f : ι → α} (g : α → β)

theorem apply_prod_le_sum_apply (h_one : g 1 ≤ 0) (h_mul : ∀ (a b : α), g (a * b) ≤ g a + g b) :
    g (∏ x ∈ s, f x) ≤ ∑ x ∈ s, g (f x) := by
  refine (Multiset.apply_prod_le_sum_map _ _ h_one h_mul).trans_eq ?_
  rw [Multiset.map_map, Function.comp_def, Finset.sum_map_val]

