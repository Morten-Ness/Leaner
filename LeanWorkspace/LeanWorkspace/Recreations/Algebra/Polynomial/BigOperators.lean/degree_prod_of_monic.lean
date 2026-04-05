import Mathlib

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable [CommSemiring R] (f : ι → R[X]) (t : Multiset R[X])

theorem degree_prod_of_monic [Nontrivial R] (h : ∀ i ∈ s, (f i).Monic) :
    (∏ i ∈ s, f i).degree = ∑ i ∈ s, (f i).degree := by
  simpa using Polynomial.degree_multiset_prod_of_monic (s.1.map f) (by simpa using h)

