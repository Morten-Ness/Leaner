import Mathlib

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

variable {R : Type*} [CommRing R]

theorem fwdDiff_iter_pow_eq_zero_of_lt {j n : ℕ} (h : j < n) :
    Δ_[1]^[n] (fun (r : R) ↦ r ^ j) = 0 := by
  induction n generalizing j with
  | zero => aesop
  | succ n ih =>
    have : (Δ_[1] fun (r : R) ↦ r ^ j) = ∑ i ∈ range j, j.choose i • fun r ↦ r ^ i := by
      ext x
      simp [nsmul_eq_mul, fwdDiff, add_pow, sum_range_succ, mul_comm]
    rw [iterate_succ_apply, this, fwdDiff_iter_finset_sum]
    exact sum_eq_zero fun i hi ↦ by
      rw [fwdDiff_iter_const_smul, ih (by have := mem_range.1 hi; lia), nsmul_zero]

