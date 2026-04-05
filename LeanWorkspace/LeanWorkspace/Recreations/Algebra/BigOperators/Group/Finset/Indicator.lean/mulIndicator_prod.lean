import Mathlib

variable {ι κ α β : Type*} [CommMonoid β]

theorem mulIndicator_prod (s : Finset ι) (t : Set κ) (f : ι → κ → β) :
    mulIndicator t (∏ i ∈ s, f i) = ∏ i ∈ s, mulIndicator t (f i) := map_prod (mulIndicatorHom _ _) _ _

