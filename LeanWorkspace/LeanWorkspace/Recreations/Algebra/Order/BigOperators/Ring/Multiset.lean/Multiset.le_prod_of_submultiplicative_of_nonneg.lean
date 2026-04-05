import Mathlib

variable {α β : Type*} [CommMonoid α] [CommMonoidWithZero β] [PartialOrder β] [PosMulMono β]

theorem Multiset.le_prod_of_submultiplicative_of_nonneg (f : α → β) (h0 : ∀ a, 0 ≤ f a)
    (h_one : f 1 ≤ 1) (h_mul : ∀ a b, f (a * b) ≤ f a * f b) (s : Multiset α) :
    f s.prod ≤ (s.map f).prod := le_prod_of_submultiplicative_on_pred_of_nonneg f (fun _ ↦ True) h0 h_one
    (fun x y _ _ ↦ h_mul x y) (by simp) s (by simp)

