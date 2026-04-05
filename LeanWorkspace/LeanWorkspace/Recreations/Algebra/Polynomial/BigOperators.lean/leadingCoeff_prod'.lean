import Mathlib

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable [CommSemiring R] (f : ι → R[X]) (t : Multiset R[X])

theorem leadingCoeff_prod' (h : (∏ i ∈ s, (f i).leadingCoeff) ≠ 0) :
    (∏ i ∈ s, f i).leadingCoeff = ∏ i ∈ s, (f i).leadingCoeff := by
  simpa using Polynomial.leadingCoeff_multiset_prod' (s.1.map f) (by simpa using h)

