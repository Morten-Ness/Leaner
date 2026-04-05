import Mathlib

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable [CommRing R]

variable [Nontrivial R]

theorem natDegree_multiset_prod_X_sub_C_eq_card (s : Multiset R) :
    (s.map (Polynomial.X - Polynomial.C ·)).prod.natDegree = Multiset.card s := by
  rw [Polynomial.natDegree_multiset_prod_of_monic, Multiset.map_map]
  · simp
  · exact Multiset.forall_mem_map_iff.2 fun a _ => Polynomial.monic_X_sub_C a

