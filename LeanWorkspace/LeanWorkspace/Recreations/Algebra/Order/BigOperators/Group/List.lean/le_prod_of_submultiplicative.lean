import Mathlib

variable {ι α M N : Type*}

variable {α β : Type*} [Monoid α] [CommMonoid β] [Preorder β] [IsOrderedMonoid β]

theorem le_prod_of_submultiplicative (f : α → β) (h_one : f 1 ≤ 1)
    (h_mul : ∀ a b, f (a * b) ≤ f a * f b) (l : List α) : f l.prod ≤ (l.map f).prod := List.le_prod_of_submultiplicative_on_pred f (fun _ => True) h_one trivial (fun x y _ _ => h_mul x y)
    (by simp) l (by simp)

