import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [CommMonoid N] [Preorder N]

variable {f g : ι → N} {s t : Finset ι}

theorem prod_le_prod_of_subset_of_one_le' [MulLeftMono N] (h : s ⊆ t)
    (hf : ∀ i ∈ t, i ∉ s → 1 ≤ f i) : ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  classical calc
      ∏ i ∈ s, f i ≤ (∏ i ∈ t \ s, f i) * ∏ i ∈ s, f i :=
        le_mul_of_one_le_left' <| Finset.one_le_prod' <| by simpa only [mem_sdiff, and_imp]
      _ = ∏ i ∈ t \ s ∪ s, f i := (prod_union sdiff_disjoint).symm
      _ = ∏ i ∈ t, f i := by rw [sdiff_union_of_subset h]

