import Mathlib

variable {α R S : Type*}

theorem map_sum [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (g : R ≃+* S)
    (f : α → R) (s : Finset α) : g (∑ x ∈ s, f x) = ∑ x ∈ s, g (f x) := map_sum g f s

