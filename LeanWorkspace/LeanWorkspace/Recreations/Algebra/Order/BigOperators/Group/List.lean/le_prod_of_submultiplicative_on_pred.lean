import Mathlib

variable {ι α M N : Type*}

variable {α β : Type*} [Monoid α] [CommMonoid β] [Preorder β] [IsOrderedMonoid β]

theorem le_prod_of_submultiplicative_on_pred (f : α → β)
    (p : α → Prop) (h_one : f 1 ≤ 1) (hp_one : p 1)
    (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b) (hp_mul : ∀ a b, p a → p b → p (a * b))
    (l : List α) (hpl : ∀ a, a ∈ l → p a) : f l.prod ≤ (l.map f).prod := by
  induction l with
  | nil => simp [h_one]
  | cons a s ih =>
    have hpla : ∀ x, x ∈ s → p x := fun x hx => hpl x (mem_cons_of_mem _ hx)
    have hp_prod : p s.prod := prod_induction p hp_mul hp_one hpla
    grw [prod_cons, map_cons, prod_cons, h_mul a s.prod (hpl _ mem_cons_self) hp_prod, ih hpla]

