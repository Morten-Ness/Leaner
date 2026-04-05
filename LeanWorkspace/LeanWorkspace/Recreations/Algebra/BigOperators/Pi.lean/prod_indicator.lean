import Mathlib

open scoped Finset

variable {ι κ M N R α : Type*}

variable [CommSemiring R]

theorem prod_indicator (s : Finset ι) (f : ι → Set κ) (g : ι → κ → R) :
    ∏ i ∈ s, (f i).indicator (g i) = (⋂ x ∈ s, f x).indicator (∏ i ∈ s, g i) := by
  ext a; simpa using prod_indicator_apply ..

