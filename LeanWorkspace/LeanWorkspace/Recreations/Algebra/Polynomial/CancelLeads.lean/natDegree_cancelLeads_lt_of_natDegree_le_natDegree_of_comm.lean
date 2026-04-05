import Mathlib

variable {R : Type*}

variable [Ring R] (p q : R[X])

theorem natDegree_cancelLeads_lt_of_natDegree_le_natDegree_of_comm
    (comm : p.leadingCoeff * q.leadingCoeff = q.leadingCoeff * p.leadingCoeff)
    (h : p.natDegree ≤ q.natDegree) (hq : 0 < q.natDegree) :
    (p.cancelLeads q).natDegree < q.natDegree := by
  by_cases hp : p = 0
  · convert hq
    simp [hp, Polynomial.cancelLeads]
  rw [Polynomial.cancelLeads, sub_eq_add_neg, tsub_eq_zero_iff_le.mpr h, pow_zero, mul_one]
  by_cases h0 :
    Polynomial.C p.leadingCoeff * q + -(Polynomial.C q.leadingCoeff * Polynomial.X ^ (q.natDegree - p.natDegree) * p) = 0
  · exact (le_of_eq (by simp only [h0, natDegree_zero])).trans_lt hq
  apply lt_of_le_of_ne
  · compute_degree!
    rwa [Nat.sub_add_cancel]
  · contrapose! h0
    rw [← leadingCoeff_eq_zero, leadingCoeff, h0, mul_assoc, X_pow_mul, ← tsub_add_cancel_of_le h,
      add_comm _ p.natDegree]
    simp only [coeff_mul_X_pow, coeff_neg, coeff_C_mul, add_tsub_cancel_left, coeff_add]
    rw [add_comm p.natDegree, tsub_add_cancel_of_le h, ← leadingCoeff, ← leadingCoeff, comm,
      add_neg_cancel]

