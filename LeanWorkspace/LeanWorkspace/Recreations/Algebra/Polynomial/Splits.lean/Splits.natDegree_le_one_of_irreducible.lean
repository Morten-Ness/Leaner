import Mathlib

variable {R : Type*}

variable [CommSemiring R]

theorem Splits.natDegree_le_one_of_irreducible {f : R[X]} (hf : Polynomial.Splits f)
    (h : Irreducible f) : natDegree f ≤ 1 := by
  nontriviality R
  obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset'.mp hf
  rcases m.empty_or_exists_mem with rfl | ⟨a, ha⟩
  · rw [hm]
    simp
  · obtain ⟨m, rfl⟩ := Multiset.exists_cons_of_mem ha
    rw [Multiset.map_cons, Multiset.prod_cons] at hm
    rw [hm] at h
    simp only [irreducible_mul_iff, IsUnit.mul_iff, not_isUnit_X_add_C, false_and, and_false,
      or_false, false_or, ← Multiset.prod_toList, List.prod_isUnit_iff] at h
    have : m = 0 := by simpa [not_isUnit_X_add_C, ← Multiset.eq_zero_iff_forall_notMem] using h.1.2
    grw [hm, this, natDegree_mul_le]
    simp

