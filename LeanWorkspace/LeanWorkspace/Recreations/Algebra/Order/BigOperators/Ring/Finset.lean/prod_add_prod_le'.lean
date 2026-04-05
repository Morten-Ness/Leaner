import Mathlib

variable {ι R S : Type*}

variable [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
  {f g h : ι → R} {s : Finset ι} {i : ι}

theorem prod_add_prod_le' (hi : i ∈ s) (h2i : g i + h i ≤ f i) (hgf : ∀ j ∈ s, j ≠ i → g j ≤ f j)
    (hhf : ∀ j ∈ s, j ≠ i → h j ≤ f j) : ((∏ i ∈ s, g i) + ∏ i ∈ s, h i) ≤ ∏ i ∈ s, f i := by
  classical
  simp_rw [prod_eq_mul_prod_diff_singleton_of_mem hi]
  grw [← h2i, right_distrib]
  gcongr with j hj j hj <;> simp_all

