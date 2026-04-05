import Mathlib

variable {ι α M N : Type*}

variable {α β : Type*} [Monoid α] [AddMonoid β] [Preorder β] [AddLeftMono β]
  (l : List α) (f : α → β)

theorem apply_prod_le_sum_map (h_one : f 1 ≤ 0) (h_mul : ∀ (a b : α), f (a * b) ≤ f a + f b) :
    f l.prod ≤ (l.map f).sum := by
  induction l with
  | nil => simp [h_one]
  | cons hd tl IH => grw [prod_cons, h_mul, IH]; simp

