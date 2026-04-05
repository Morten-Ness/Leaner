import Mathlib

variable {ι α M N : Type*}

variable {α β : Type*} [Monoid α] [CommMonoid β] [Preorder β] [IsOrderedMonoid β]

theorem le_prod_nonempty_of_submultiplicative (f : α → β) (h_mul : ∀ a b, f (a * b) ≤ f a * f b)
    (l : List α) (hs_nonempty : l ≠ ∅) : f l.prod ≤ (l.map f).prod := List.le_prod_nonempty_of_submultiplicative_on_pred f (fun _ => True) (by simp [h_mul]) (by simp) l
    hs_nonempty (by simp)

