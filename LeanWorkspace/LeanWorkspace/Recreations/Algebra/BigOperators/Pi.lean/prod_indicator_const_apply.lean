import Mathlib

open scoped Finset

variable {ι κ M N R α : Type*}

variable [CommSemiring R]

theorem prod_indicator_const_apply (s : Finset ι) (f : ι → Set κ) (g : κ → R) (j : κ) :
    ∏ i ∈ s, (f i).indicator g j = (⋂ x ∈ s, f x).indicator (g ^ #s) j := by
  simp [prod_indicator_apply]

