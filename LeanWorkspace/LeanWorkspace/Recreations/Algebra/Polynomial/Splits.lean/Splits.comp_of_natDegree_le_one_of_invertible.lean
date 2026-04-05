import Mathlib

variable {R : Type*}

variable [CommSemiring R]

theorem Splits.comp_of_natDegree_le_one_of_invertible {f g : R[X]} (hf : f.Splits)
    (hg : g.natDegree ≤ 1) (h : Invertible g.leadingCoeff) : (f.comp g).Splits := by
  rcases lt_or_eq_of_le hg with hg | hg
  · rw [eq_C_of_natDegree_eq_zero (Nat.lt_one_iff.mp hg)]
    simp
  obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset'.mp hf
  rw [hm, mul_comp, C_comp, multiset_prod_comp]
  refine (Polynomial.Splits.C _).mul (multisetProd ?_)
  simp only [Multiset.mem_map]
  rintro - ⟨-, ⟨a, -, rfl⟩, rfl⟩
  apply Polynomial.splits_of_natDegree_le_one_of_invertible (by simpa)
  rw [leadingCoeff, hg] at h
  simpa [leadingCoeff, hg]

