import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommSemiring R]

variable [DecidableEq ι]

theorem prod_sum {κ : ι → Type*} [∀ i, Fintype (κ i)] (f : ∀ i, κ i → R) :
    ∏ i, ∑ j, f i j = ∑ x : ∀ i, κ i, ∏ i, f i (x i) := Finset.prod_univ_sum _ _

