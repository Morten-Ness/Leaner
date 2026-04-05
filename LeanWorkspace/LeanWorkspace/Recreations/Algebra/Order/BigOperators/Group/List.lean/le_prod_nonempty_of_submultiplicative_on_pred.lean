import Mathlib

variable {ι α M N : Type*}

variable {α β : Type*} [Monoid α] [CommMonoid β] [Preorder β] [IsOrderedMonoid β]

theorem le_prod_nonempty_of_submultiplicative_on_pred (f : α → β) (p : α → Prop)
    (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b) (hp_mul : ∀ a b, p a → p b → p (a * b))
    (l : List α) (hl_nonempty : l ≠ []) (hl : ∀ a, a ∈ l → p a) : f l.prod ≤ (l.map f).prod := by
  induction l with
  | nil => simp at hl_nonempty
  | cons a l ih =>
    rw [prod_cons, map_cons, prod_cons]
    by_cases hl_empty : l = []
    · simp [hl_empty]
    have hla_restrict : ∀ x, x ∈ l → p x := fun x hx => hl x (mem_cons_of_mem _ hx)
    have hp_sup : p l.prod := prod_induction_nonempty p hp_mul hl_empty hla_restrict
    have hp_a : p a := hl a mem_cons_self
    grw [h_mul a _ hp_a hp_sup, ← ih hl_empty hla_restrict]

