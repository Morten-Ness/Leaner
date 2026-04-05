import Mathlib

variable {ι R S : Type*}

variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {f g : ι → R} {s t : Finset ι}

theorem le_prod_of_submultiplicative_of_nonneg {M : Type*} [CommMonoid M]
    (f : M → R) (h_nonneg : ∀ a, 0 ≤ f a) (h_one : f 1 ≤ 1)
    (h_mul : ∀ x y : M, f (x * y) ≤ f x * f y) (s : Finset ι) (g : ι → M) :
    f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i) := le_trans (Multiset.le_prod_of_submultiplicative_of_nonneg f h_nonneg h_one h_mul _)
    (by simp [Multiset.map_map])

