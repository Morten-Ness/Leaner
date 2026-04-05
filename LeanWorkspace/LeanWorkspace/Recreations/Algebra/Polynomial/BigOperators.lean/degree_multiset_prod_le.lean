import Mathlib

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable [CommSemiring R] (f : ι → R[X]) (t : Multiset R[X])

theorem degree_multiset_prod_le : t.prod.degree ≤ (t.map Polynomial.degree).sum := Quotient.inductionOn t (by simpa using Polynomial.degree_list_prod_le)

