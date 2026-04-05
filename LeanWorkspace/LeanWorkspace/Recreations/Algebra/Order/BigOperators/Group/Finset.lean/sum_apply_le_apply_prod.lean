import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid α] [AddCommMonoid β] [Preorder β] [AddLeftMono β]
  (s : Finset ι) {f : ι → α} (g : α → β)

theorem sum_apply_le_apply_prod (h_one : 0 ≤ g 1) (h_mul : ∀ (a b : α), g a + g b ≤ g (a * b)) :
    ∑ x ∈ s, g (f x) ≤ g (∏ x ∈ s, f x) := Finset.apply_prod_le_sum_apply s (β := βᵒᵈ) g h_one h_mul

