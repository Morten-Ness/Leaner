import Mathlib

open scoped Finset

variable {ι κ M N R α : Type*}

variable [CommSemiring R]

theorem prod_indicator_const (s : Finset ι) (f : ι → Set κ) (g : κ → R) :
    ∏ i ∈ s, (f i).indicator g = (⋂ x ∈ s, f x).indicator (g ^ #s) := by simp [prod_indicator]

