import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [Preorder M] [CanonicallyOrderedMul M] {f : ι → M} {s t : Finset ι}

theorem prod_le_prod_of_ne_one' (h : ∀ x ∈ s, f x ≠ 1 → x ∈ t) :
    ∏ x ∈ s, f x ≤ ∏ x ∈ t, f x := by
  have := CanonicallyOrderedMul.toIsOrderedMonoid (α := M)
  classical calc
    ∏ x ∈ s, f x = (∏ x ∈ s with f x = 1, f x) * ∏ x ∈ s with f x ≠ 1, f x := by
      rw [← prod_union, filter_union_filter_not_eq]
      exact disjoint_filter.2 fun _ _ h n_h ↦ n_h h
    _ ≤ ∏ x ∈ t, f x :=
      mul_le_of_le_one_of_le
        (Finset.prod_le_one' <| by simp only [mem_filter, and_imp]; exact fun _ _ ↦ le_of_eq)
        (Finset.prod_le_prod_of_subset' <| by simpa only [subset_iff, mem_filter, and_imp])

