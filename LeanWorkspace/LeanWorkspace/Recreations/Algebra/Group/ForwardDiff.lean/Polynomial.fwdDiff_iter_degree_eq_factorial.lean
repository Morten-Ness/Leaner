import Mathlib

open scoped Polynomial

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

variable {R : Type*} [CommRing R]

theorem Polynomial.fwdDiff_iter_degree_eq_factorial (P : R[X]) :
    Δ_[1]^[P.natDegree] P.eval = P.leadingCoeff • P.natDegree ! := funext fun x ↦ by
  simp_rw [P.eval_eq_sum_range, ← sum_apply _ _ (fun i x ↦ P.coeff i * x ^ i),
    fwdDiff_iter_finset_sum, ← smul_eq_mul, ← Pi.smul_def, fwdDiff_iter_const_smul, Pi.smul_apply]
  rw [sum_apply, sum_range_succ, sum_eq_zero (fun i hi ↦ ?_), zero_add,
    fwdDiff_iter_eq_factorial, leadingCoeff, Pi.smul_apply]
  rw [fwdDiff_iter_pow_eq_zero_of_lt (mem_range.mp hi), smul_zero, Pi.zero_apply]

