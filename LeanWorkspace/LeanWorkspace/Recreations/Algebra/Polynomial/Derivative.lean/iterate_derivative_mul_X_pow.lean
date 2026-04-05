import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommSemiring R]

theorem iterate_derivative_mul_X_pow (n m : ℕ) (p : R[X]) :
    Polynomial.derivative^[n] (p * Polynomial.X ^ m) =
      ∑ k ∈ range (min m n).succ,
        (n.choose k * m.descFactorial k) • (Polynomial.derivative^[n - k] p * Polynomial.X ^ (m - k)) := by
  have hsum : Polynomial.derivative^[n] (p * Polynomial.X ^ m) =
      ∑ k ∈ range n.succ,
        (n.choose k * m.descFactorial k) • (Polynomial.derivative^[n - k] p * Polynomial.X ^ (m - k)) := by
    simp_rw [Polynomial.iterate_derivative_mul, Polynomial.iterate_derivative_X_pow_eq_smul, mul_smul]
    congr! 2 with k hk
    norm_cast
    ring
  rw [hsum]
  refine sum_congr_of_eq_on_inter (fun k hk hk' ↦ ?_) (by simp_all) (by simp)
  rcases le_or_gt k m with hkm | hkm
  · replace hk' : n < k := by simpa [hkm] using hk'
    simp [Nat.choose_eq_zero_of_lt hk']
  · simp [Nat.descFactorial_eq_zero_iff_lt.mpr hkm]

