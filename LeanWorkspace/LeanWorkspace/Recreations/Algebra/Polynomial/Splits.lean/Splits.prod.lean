import Mathlib

variable {R : Type*}

variable [CommSemiring R]

theorem Splits.prod {ι : Type*} {f : ι → R[X]} {s : Finset ι}
    (h : ∀ i ∈ s, Polynomial.Splits (f i)) : Polynomial.Splits (∏ i ∈ s, f i) := prod_mem h

