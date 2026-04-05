import Mathlib

variable {ι α M N : Type*}

variable {α β : Type*} [Monoid α] [AddMonoid β] [Preorder β] [AddLeftMono β]
  (l : List α) (f : α → β)

theorem sum_map_le_apply_prod (h_one : 0 ≤ f 1) (h_mul : ∀ (a b : α), f a + f b ≤ f (a * b)) :
    (l.map f).sum ≤ f l.prod := List.apply_prod_le_sum_map (β := βᵒᵈ) l f h_one h_mul

