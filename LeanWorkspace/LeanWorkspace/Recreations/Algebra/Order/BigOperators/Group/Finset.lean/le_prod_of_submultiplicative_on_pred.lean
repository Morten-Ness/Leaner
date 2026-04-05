import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [CommMonoid N] [Preorder N]

theorem le_prod_of_submultiplicative_on_pred [IsOrderedMonoid N] (f : M → N) (p : M → Prop)
    (h_one : f 1 ≤ 1) (h_mul : ∀ x y, p x → p y → f (x * y) ≤ f x * f y)
    (hp_mul : ∀ x y, p x → p y → p (x * y)) (g : ι → M) {s : Finset ι} (hs : ∀ i ∈ s, p (g i)) :
    f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i) := by
  rcases eq_empty_or_nonempty s with (rfl | hs_nonempty)
  · simp [h_one]
  · exact Finset.le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul g s hs_nonempty hs

