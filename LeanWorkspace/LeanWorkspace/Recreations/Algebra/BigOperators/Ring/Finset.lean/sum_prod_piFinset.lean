import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [CommSemiring R]

variable [DecidableEq ι]

theorem sum_prod_piFinset [Fintype ι] (s : Finset κ) (g : ι → κ → R) :
    ∑ f ∈ piFinset fun _ : ι ↦ s, ∏ i, g i (f i) = ∏ i, ∑ j ∈ s, g i j := by
  rw [← Finset.prod_univ_sum]

