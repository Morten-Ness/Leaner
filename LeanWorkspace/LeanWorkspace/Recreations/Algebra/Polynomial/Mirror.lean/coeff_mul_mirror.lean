import Mathlib

variable {R : Type*} [Semiring R] (p q : R[X])

theorem coeff_mul_mirror :
    (p * p.mirror).coeff (p.natDegree + p.natTrailingDegree) = p.sum fun _ => (· ^ 2) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine
    (Finset.sum_congr rfl fun n hn => ?_).trans
      (p.sum_eq_of_subset (fun _ ↦ (· ^ 2)) (fun _ ↦ zero_pow two_ne_zero) fun n hn ↦
          Finset.mem_range_succ_iff.mpr
            ((le_natDegree_of_mem_supp n hn).trans (Nat.le_add_right _ _))).symm
  rw [Polynomial.coeff_mirror, ← revAt_le (Finset.mem_range_succ_iff.mp hn), revAt_invol, ← sq]

