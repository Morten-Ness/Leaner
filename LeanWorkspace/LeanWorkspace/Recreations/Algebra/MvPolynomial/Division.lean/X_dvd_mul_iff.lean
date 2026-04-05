import Mathlib

variable {σ R : Type*} [CommSemiring R]

variable {R : Type*} [CommRing R] {i : σ} {p q r : MvPolynomial σ R}

theorem X_dvd_mul_iff [IsCancelMulZero R] :
    X i ∣ p * q ↔ X i ∣ p ∨ X i ∣ q := by
  nontriviality R
  have _ : NoZeroDivisors (MvPolynomial σ R) :=
    IsLeftCancelMulZero.to_noZeroDivisors (MvPolynomial σ R)
  constructor
  · intro h
    suffices (p.modMonomial (Finsupp.single i 1)) * (q.modMonomial (Finsupp.single i 1)) =
          (p * q).modMonomial (Finsupp.single i 1) by
      simp only [MvPolynomial.X_dvd_iff_modMonomial_eq_zero] at h ⊢
      rwa [h, mul_eq_zero] at this
    have hp := MvPolynomial.modMonomial_add_divMonomial_single p i
    have hq := MvPolynomial.modMonomial_add_divMonomial_single q i
    rw [MvPolynomial.eq_modMonomial_single_iff]
    · intro n
      contrapose
      intro hn
      classical
      rw [notMem_support_iff, coeff_mul]
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Finset.mem_antidiagonal] at hx
      simp only [← hx, Finsupp.coe_add, Pi.add_apply, Nat.add_eq_zero_iff, not_and_or] at hn
      rcases hn with hn | hn
      · rw [MvPolynomial.coeff_modMonomial_of_le, zero_mul]
        simpa [← Nat.one_le_iff_ne_zero] using hn
      · rw [mul_comm, MvPolynomial.coeff_modMonomial_of_le, zero_mul]
        simpa [← Nat.one_le_iff_ne_zero] using hn
    · nth_rewrite 1 [← hp]
      nth_rewrite 1 [← hq]
      simp only [add_mul, mul_add, add_assoc, add_sub_cancel_left]
      simp only [← mul_assoc, mul_comm _ (X i)]
      simp only [mul_assoc, ← mul_add (X i)]
      apply dvd_mul_right
  · rintro (h | h)
    · exact dvd_mul_of_dvd_left h q
    · exact dvd_mul_of_dvd_right h p

