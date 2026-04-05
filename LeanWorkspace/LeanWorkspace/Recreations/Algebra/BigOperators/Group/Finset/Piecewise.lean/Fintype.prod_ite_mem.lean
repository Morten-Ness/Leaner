import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M] [Fintype ι]

variable [DecidableEq ι]

theorem prod_ite_mem (s : Finset ι) (f : ι → M) : ∏ i, (if i ∈ s then f i else 1) = ∏ i ∈ s, f i := by
  simp

