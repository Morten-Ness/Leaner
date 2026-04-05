import Mathlib

variable {ι α β : Type*}

variable [CommMonoid α] [CommMonoid β] [Preorder β] [IsOrderedMonoid β]

theorem le_prod_of_submultiplicative_on_pred (f : α → β)
    (p : α → Prop) (h_one : f 1 ≤ 1) (hp_one : p 1)
    (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b) (hp_mul : ∀ a b, p a → p b → p (a * b))
    (s : Multiset α) (hps : ∀ a, a ∈ s → p a) : f s.prod ≤ (s.map f).prod := by
  induction s using Quotient.inductionOn with
  | h l => simp [l.le_prod_of_submultiplicative_on_pred f p h_one hp_one h_mul hp_mul (by simpa)]

