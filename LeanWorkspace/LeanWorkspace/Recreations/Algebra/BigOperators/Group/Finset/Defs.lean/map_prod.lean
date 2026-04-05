import Mathlib

variable {ι κ M N G α : Type*}

theorem map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G M N] [MonoidHomClass G M N]
    (g : G) (f : ι → M) (s : Finset ι) : g (∏ x ∈ s, f x) = ∏ x ∈ s, g (f x) := by
  simp only [Finset.prod_eq_multiset_prod, map_multiset_prod, Multiset.map_map]; rfl

