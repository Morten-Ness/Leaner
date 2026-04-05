import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [Preorder M] [IsOrderedCancelMonoid M] {f g : ι → M} {s t : Finset ι}

theorem prod_lt_prod_of_subset' [MulLeftStrictMono M] (h : s ⊆ t) {i : ι} (ht : i ∈ t)
  (hs : i ∉ s) (hlt : 1 < f i)
    (hle : ∀ j ∈ t, j ∉ s → 1 ≤ f j) : ∏ j ∈ s, f j < ∏ j ∈ t, f j := by
  classical calc
    ∏ j ∈ s, f j < ∏ j ∈ insert i s, f j := by
      rw [prod_insert hs]
      exact lt_mul_of_one_lt_left' (∏ j ∈ s, f j) hlt
    _ ≤ ∏ j ∈ t, f j := by
      apply Finset.prod_le_prod_of_subset_of_one_le'
      · simp [Finset.insert_subset_iff, h, ht]
      · intro x hx h'x
        simp only [mem_insert, not_or] at h'x
        exact hle x hx h'x.2

