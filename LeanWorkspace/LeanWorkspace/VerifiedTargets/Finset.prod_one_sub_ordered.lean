import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [CommRing R]

theorem prod_one_sub_ordered [LinearOrder ι] (s : Finset ι) (f : ι → R) :
    ∏ i ∈ s, (1 - f i) = 1 - ∑ i ∈ s, f i * ∏ j ∈ s with j < i, (1 - f j) := by
  rw [Finset.prod_sub_ordered]
  simp

