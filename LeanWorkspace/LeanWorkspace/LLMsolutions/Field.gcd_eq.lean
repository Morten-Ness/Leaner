FAIL
import Mathlib

variable {K : Type*} [Field K]

theorem gcd_eq [DecidableEq K] (a b : K) :
    EuclideanDomain.gcd a b = if a = 0 then b else a := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [if_neg ha]
    have hdiv : EuclideanDomain.gcd a b ∣ a := EuclideanDomain.gcd_dvd_left a b
    rcases hdiv with ⟨c, rfl⟩
    by_cases hg : EuclideanDomain.gcd a b = 0
    · exfalso
      exact ha (by simpa [hg])
    · have hcu : IsUnit c := isUnit_iff_ne_zero.mpr <| by
        intro hc
        apply ha
        simp [hc]
      have hgu : IsUnit (EuclideanDomain.gcd a b) := by
        rw [← mul_one (EuclideanDomain.gcd a b)]
        exact isUnit_iff_dvd_one.mpr <| by
          refine ⟨c * c⁻¹, ?_⟩
          field_simp [hg]
      exact hgu.eq_mul_inv_cancel <| by simpa using ha
