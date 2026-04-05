import Mathlib

variable {ι α β : Type*}

variable [CommMonoid α] [CommMonoid β] [Preorder β] [IsOrderedMonoid β]

theorem le_prod_of_submultiplicative (f : α → β) (h_one : f 1 ≤ 1)
    (h_mul : ∀ a b, f (a * b) ≤ f a * f b) (s : Multiset α) : f s.prod ≤ (s.map f).prod := by
  induction s using Quotient.inductionOn with
  | h l => simp [l.le_prod_of_submultiplicative f h_one h_mul]

