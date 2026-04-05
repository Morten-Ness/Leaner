import Mathlib

variable {ι α β : Type*}

variable [CommMonoid α] [AddCommMonoid β] [Preorder β] [AddLeftMono β] (m : Multiset α) (f : α → β)

theorem sum_map_le_apply_prod (h_one : 0 ≤ f 1) (h_mul : ∀ (a b : α), f a + f b ≤ f (a * b)) :
    (m.map f).sum ≤ f m.prod := Multiset.apply_prod_le_sum_map m (β := βᵒᵈ) f h_one h_mul

