import Mathlib

variable {ι R S : Type*}

variable [CommMonoidWithZero R]

variable [Preorder R] [ZeroLEOneClass R] [PosMulMono R] {f g : ι → R} {s t : Finset ι}

theorem prod_le_prod_of_subset_of_le_one (h : s ⊆ t) (hf0 : ∀ i ∈ t, 0 ≤ f i)
    (hf : ∀ i ∈ t, i ∉ s → f i ≤ 1) :
    ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i := by
  have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
  classical
  calc
    ∏ i ∈ t, f i = ∏ i ∈ t \ s ∪ s, f i := by rw [sdiff_union_of_subset h]
    _ = (∏ i ∈ t \ s, f i) * ∏ i ∈ s, f i := prod_union sdiff_disjoint
    _ ≤ ∏ i ∈ s, f i :=
      mul_le_of_le_one_left (Finset.prod_nonneg (by grind)) (Finset.prod_le_one (by grind) (by grind))

