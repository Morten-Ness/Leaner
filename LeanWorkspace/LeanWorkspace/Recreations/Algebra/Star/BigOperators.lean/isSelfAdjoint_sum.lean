import Mathlib

variable {R : Type*}

theorem isSelfAdjoint_sum {ι : Type*} [AddCommMonoid R] [StarAddMonoid R] (s : Finset ι)
    {x : ι → R} (h : ∀ i ∈ s, IsSelfAdjoint (x i)) : IsSelfAdjoint (∑ i ∈ s, x i) := by
  simpa [IsSelfAdjoint, star_sum] using Finset.sum_congr rfl fun _ hi => h _ hi

