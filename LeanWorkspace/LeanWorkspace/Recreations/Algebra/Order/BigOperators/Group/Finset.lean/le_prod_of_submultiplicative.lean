import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [CommMonoid N] [Preorder N]

theorem le_prod_of_submultiplicative [IsOrderedMonoid N] (f : M → N) (h_one : f 1 ≤ 1)
    (h_mul : ∀ x y, f (x * y) ≤ f x * f y) (s : Finset ι) (g : ι → M) :
    f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i) := le_trans (Multiset.le_prod_of_submultiplicative f h_one h_mul _) (by simp)

