import Mathlib

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable [CommRing R]

theorem multiset_prod_X_sub_C_coeff_card_pred (t : Multiset R) (ht : 0 < Multiset.card t) :
    (t.map fun x => Polynomial.X - Polynomial.C x).prod.coeff ((Multiset.card t) - 1) = -t.sum := by
  nontriviality R
  convert Polynomial.multiset_prod_X_sub_C_nextCoeff (by assumption)
  rw [nextCoeff, if_neg]
  swap
  · rw [Polynomial.natDegree_multiset_prod_of_monic]
    swap
    · simp only [Multiset.mem_map]
      rintro _ ⟨_, _, rfl⟩
      apply Polynomial.monic_X_sub_C
    simp_rw [Multiset.sum_eq_zero_iff, Multiset.mem_map]
    obtain ⟨x, hx⟩ := card_pos_iff_exists_mem.mp ht
    exact fun h => one_ne_zero <| h 1 ⟨_, ⟨x, hx, rfl⟩, Polynomial.natDegree_X_sub_C _⟩
  congr; rw [Polynomial.natDegree_multiset_prod_of_monic] <;> · simp [Polynomial.monic_X_sub_C]

