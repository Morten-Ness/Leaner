import Mathlib

variable {ι R S : Type*}

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {f : ι → R} {s : Finset ι}

theorem sum_sq_le_sq_sum_of_nonneg (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  simp only [sq, sum_mul_sum]
  refine sum_le_sum fun i hi ↦ ?_
  rw [← mul_sum]
  gcongr
  · exact hf i hi
  · exact single_le_sum hf hi

