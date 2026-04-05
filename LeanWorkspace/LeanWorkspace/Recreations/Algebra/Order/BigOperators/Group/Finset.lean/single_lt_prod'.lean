import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [Preorder M] [IsOrderedCancelMonoid M] {f g : ι → M} {s t : Finset ι}

theorem single_lt_prod' [MulLeftStrictMono M] {i j : ι} (hij : j ≠ i) (hi : i ∈ s) (hj : j ∈ s)
    (hlt : 1 < f j) (hle : ∀ k ∈ s, k ≠ i → 1 ≤ f k) : f i < ∏ k ∈ s, f k := calc
    f i = ∏ k ∈ {i}, f k := by rw [prod_singleton]
    _ < ∏ k ∈ s, f k :=
      Finset.prod_lt_prod_of_subset' (singleton_subset_iff.2 hi) hj (mt mem_singleton.1 hij) hlt
        fun k hks hki ↦ hle k hks (mt mem_singleton.2 hki)

