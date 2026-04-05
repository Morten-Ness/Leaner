import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommSemiring R]

variable [DecidableEq ι]

theorem prod_add (f g : ι → R) : ∏ a, (f a + g a) = ∑ t, (∏ a ∈ t, f a) * ∏ a ∈ tᶜ, g a := by
  simpa [compl_eq_univ_sdiff] using Finset.prod_add f g Finset.univ

