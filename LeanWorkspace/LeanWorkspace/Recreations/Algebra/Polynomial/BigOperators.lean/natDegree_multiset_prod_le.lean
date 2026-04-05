import Mathlib

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable [CommSemiring R] (f : ι → R[X]) (t : Multiset R[X])

theorem natDegree_multiset_prod_le : t.prod.natDegree ≤ (t.map natDegree).sum := Quotient.inductionOn t (by simpa using Polynomial.natDegree_list_prod_le)

