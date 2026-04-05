import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [CommSemiring R]

variable [DecidableEq ι]

theorem prod_univ_sum {κ : ι → Type*} [Fintype ι] (t : ∀ i, Finset (κ i)) (f : ∀ i, κ i → R) :
    ∏ i, ∑ j ∈ t i, f i j = ∑ x ∈ piFinset t, ∏ i, f i (x i) := by
  simp only [prod_attach_univ, Finset.prod_sum, Finset.sum_univ_pi]

