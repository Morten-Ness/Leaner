import Mathlib

variable {ι α β M N G k R : Type*}

theorem abs_sum_of_nonneg' {G : Type*} [AddCommGroup G] [LinearOrder G] [AddLeftMono G]
    {f : ι → G} {s : Finset ι}
    (hf : ∀ i, 0 ≤ f i) : |∑ i ∈ s, f i| = ∑ i ∈ s, f i := by
  rw [abs_of_nonneg (Finset.sum_nonneg' hf)]

