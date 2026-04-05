import Mathlib

variable {α β : Type*} [CommMonoid α] [CommMonoidWithZero β] [PartialOrder β] [PosMulMono β]

theorem Multiset.le_prod_of_submultiplicative_on_pred_of_nonneg (f : α → β) (p : α → Prop)
    (h0 : ∀ a, 0 ≤ f a) (h_one : f 1 ≤ 1) (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b)
    (hp_mul : ∀ a b, p a → p b → p (a * b)) (s : Multiset α) (hps : ∀ a, a ∈ s → p a) :
    f s.prod ≤ (s.map f).prod := by
  revert s
  refine Multiset.induction (by simp [h_one]) ?_
  intro a s hs hpsa
  by_cases hs0 : s = ∅
  · simp [hs0]
  · have hps : ∀ x, x ∈ s → p x := fun x hx ↦ hpsa x (mem_cons_of_mem hx)
    have hp_prod : p s.prod := prod_induction_nonempty p hp_mul hs0 hps
    rw [prod_cons, map_cons, prod_cons]
    exact (h_mul a s.prod (hpsa a (mem_cons_self a s)) hp_prod).trans
      (mul_le_mul_of_nonneg_left (hs hps) (h0 _))

