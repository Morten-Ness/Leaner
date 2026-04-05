import Mathlib

variable {R : Type*}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommRing R] [NoZeroDivisors R] {p q r : MvPolynomial σ R}

theorem dvd_smul_X_iff_exists {i : σ} {r : R} (hr : r ≠ 0) :
    p ∣ r • X i ↔ ∃ s, s ∣ r ∧ (p = C s ∨ p = s • X i) := by
  rw [X, smul_monomial, smul_eq_mul, mul_one, MvPolynomial.dvd_monomial_iff_exists hr, exists_comm]
  apply exists_congr
  intro b
  constructor
  · rintro ⟨m, hmn, hb, rfl⟩
    simp only [hb, true_and]
    suffices m = 0 ∨ m = Finsupp.single i 1 by
      apply this.imp <;> simp +contextual [smul_monomial, smul_eq_mul, mul_one]
    by_cases hm : m i = 0
    · left
      ext j
      simp only [Finsupp.coe_zero, Pi.zero_apply, ← Nat.le_zero]
      by_cases hj : j = i
      · rw [← hm, hj]
      · exact (hmn j).trans (Finsupp.single_eq_of_ne hj).le
    · right
      ext j
      apply le_antisymm (hmn j)
      by_cases hj : j = i
      · simpa [hj, Nat.one_le_iff_ne_zero]
      · simp [Finsupp.single_eq_of_ne hj]
  · rintro ⟨hb, hp | hp⟩
    · use 0; simp [hb, hp]
    · use Finsupp.single i 1, le_rfl, hb
      simp [hp, smul_monomial]

