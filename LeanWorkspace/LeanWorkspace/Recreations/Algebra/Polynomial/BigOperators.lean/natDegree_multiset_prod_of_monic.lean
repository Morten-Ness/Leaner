import Mathlib

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable [CommSemiring R] (f : ι → R[X]) (t : Multiset R[X])

theorem natDegree_multiset_prod_of_monic (h : ∀ f ∈ t, Polynomial.Monic f) :
    t.prod.natDegree = (t.map natDegree).sum := by
  nontriviality R
  apply Polynomial.natDegree_multiset_prod'
  simp_all

