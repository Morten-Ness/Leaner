import Mathlib

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

variable {R : Type*} [CommRing R]

theorem fwdDiff_iter_sum_mul_pow_eq_zero {n : ℕ} (P : ℕ → R) :
    Δ_[1]^[n] (fun r : R ↦ ∑ k ∈ range n, P k * r ^ k) = 0 := by
  simp_rw [← sum_apply _ _ (fun i x ↦ P i * x ^ i), fwdDiff_iter_finset_sum, sum_fn, ← smul_eq_mul,
    ← Pi.smul_def, fwdDiff_iter_const_smul, ← sum_fn]
  exact sum_eq_zero fun i hi ↦ smul_eq_zero_of_right _ <| fwdDiff_iter_pow_eq_zero_of_lt
    <| mem_range.mp hi

