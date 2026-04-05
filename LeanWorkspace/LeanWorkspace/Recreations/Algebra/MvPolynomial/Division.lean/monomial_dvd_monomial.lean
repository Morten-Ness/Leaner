import Mathlib

variable {σ R : Type*} [CommSemiring R]

theorem monomial_dvd_monomial {r s : R} {i j : σ →₀ ℕ} :
    monomial i r ∣ monomial j s ↔ (s = 0 ∨ i ≤ j) ∧ r ∣ s := by
  constructor
  · rintro ⟨x, hx⟩
    rw [MvPolynomial.ext_iff] at hx
    have hj := hx j
    have hi := hx i
    classical
    simp_rw [coeff_monomial, if_pos] at hj hi
    simp_rw [coeff_monomial_mul'] at hi hj
    split_ifs at hj with hi
    · exact ⟨Or.inr hi, _, hj⟩
    · exact ⟨Or.inl hj, hj.symm ▸ dvd_zero _⟩
  · rintro ⟨h | hij, d, rfl⟩
    · simp_rw [h, monomial_zero, dvd_zero]
    · refine ⟨monomial (j - i) d, ?_⟩
      rw [monomial_mul, add_tsub_cancel_of_le hij]

