import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_ite_mem [DecidableEq ι] (s t : Finset ι) (f : ι → M) :
    ∏ i ∈ s, (if i ∈ t then f i else 1) = ∏ i ∈ s ∩ t, f i := by
  classical
  refine Finset.induction_on s ?h0 ?hstep
  · simp
  · intro a s ha hs
    simp [ha, hs, Finset.mem_inter]
