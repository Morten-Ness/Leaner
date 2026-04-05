import Mathlib

variable {ι α β : Type*}

variable [CommMonoid α] [CommMonoid β] [Preorder β] [IsOrderedMonoid β]

theorem le_prod_nonempty_of_submultiplicative_on_pred (f : α → β) (p : α → Prop)
    (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b) (hp_mul : ∀ a b, p a → p b → p (a * b))
    (s : Multiset α) (hs_nonempty : s ≠ ∅) (hs : ∀ a, a ∈ s → p a) : f s.prod ≤ (s.map f).prod := by
  induction s using Quotient.inductionOn with
  | h l =>
    simp [l.le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul
      (by simpa using hs_nonempty) (by simpa)]

