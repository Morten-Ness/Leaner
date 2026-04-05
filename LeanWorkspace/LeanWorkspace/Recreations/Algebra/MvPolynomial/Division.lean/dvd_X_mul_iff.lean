import Mathlib

variable {σ R : Type*} [CommSemiring R]

variable {R : Type*} [CommRing R] {i : σ} {p q r : MvPolynomial σ R}

theorem dvd_X_mul_iff [IsCancelMulZero R] :
    p ∣ X i * q ↔ p ∣ q ∨ (X i ∣ p ∧ p.divMonomial (Finsupp.single i 1) ∣ q) := by
  constructor
  · rintro ⟨r, hp⟩
    have : X i ∣ p ∨ X i ∣ r := by simp [← MvPolynomial.X_dvd_mul_iff, ← hp]
    apply this.symm.imp
    · rintro ⟨r, rfl⟩
      obtain rfl : q = p * r := by rw [← X_mul_cancel_left_iff (i := i), hp, mul_left_comm]
      exact dvd_mul_right p r
    · intro hip
      refine ⟨hip, ?_⟩
      rw [MvPolynomial.X_dvd_iff_modMonomial_eq_zero] at hip
      rw [← MvPolynomial.modMonomial_add_divMonomial_single p i, hip,
        zero_add, mul_assoc, X_mul_cancel_left_iff] at hp
      use r
  · rintro (hp | ⟨hi, hq⟩)
    · exact dvd_mul_of_dvd_right hp (X i)
    · suffices p = X i * p.divMonomial (Finsupp.single i 1) by
        rw [this]
        exact mul_dvd_mul_left (X i) hq
      conv_lhs => rw [← MvPolynomial.modMonomial_add_divMonomial p (Finsupp.single i 1)]
      simpa only [← C_mul_X_eq_monomial, C_1, one_mul, add_eq_right,
        ← MvPolynomial.X_dvd_iff_modMonomial_eq_zero]

