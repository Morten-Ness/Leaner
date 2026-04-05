import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [CommSemiring R]

theorem prod_add_one {f : ι → R} (s : Finset ι) :
    ∏ i ∈ s, (f i + 1) = ∑ t ∈ s.powerset, ∏ i ∈ t, f i := by
  classical simp only [Finset.prod_add, prod_const_one, mul_one]

