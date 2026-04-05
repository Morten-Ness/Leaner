import Mathlib

variable {ι α β : Type*}

variable [CommMonoid α] [AddCommMonoid β] [Preorder β] [AddLeftMono β] (m : Multiset α) (f : α → β)

theorem apply_prod_le_sum_map (h_one : f 1 ≤ 0) (h_mul : ∀ (a b : α), f (a * b) ≤ f a + f b) :
    f m.prod ≤ (m.map f).sum := by
  induction m using Quotient.inductionOn with
  | h l => simp [l.apply_prod_le_sum_map _ h_one h_mul]

