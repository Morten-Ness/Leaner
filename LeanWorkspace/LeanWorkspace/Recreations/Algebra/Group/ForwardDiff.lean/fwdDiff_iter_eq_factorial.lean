import Mathlib

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

variable {R : Type*} [CommRing R]

theorem fwdDiff_iter_eq_factorial {n : ℕ} :
    Δ_[1]^[n] (fun (r : R) ↦ r ^ n) = n ! := by
  induction n with
  | zero => aesop
  | succ n IH =>
    have : (Δ_[1] fun (r : R) ↦ r ^ (n + 1)) =
      ∑ i ∈ range (n + 1), (n + 1).choose i • fun r ↦ r ^ i := by
      ext x
      simp [nsmul_eq_mul, fwdDiff, add_pow, sum_range_succ, mul_comm]
    simp_rw [iterate_succ_apply, this, fwdDiff_iter_finset_sum, fwdDiff_iter_const_smul,
       sum_range_succ]
    simpa [IH, factorial_succ] using sum_eq_zero fun i hi ↦ by
      rw [fwdDiff_iter_pow_eq_zero_of_lt (by have := mem_range.1 hi; lia), mul_zero]

