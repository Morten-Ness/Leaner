import Mathlib

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable [CommSemiring R] (f : ι → R[X]) (t : Multiset R[X])

theorem natDegree_multiset_prod' (h : (t.map fun f => leadingCoeff f).prod ≠ 0) :
    t.prod.natDegree = (t.map fun f => natDegree f).sum := by
  revert h
  refine Multiset.induction_on t ?_ fun a t ih ht => ?_; · simp
  rw [Multiset.map_cons, Multiset.prod_cons] at ht ⊢
  rw [Multiset.sum_cons, Polynomial.natDegree_mul', ih]
  · apply right_ne_zero_of_mul ht
  · rwa [Polynomial.leadingCoeff_multiset_prod']
    apply right_ne_zero_of_mul ht

