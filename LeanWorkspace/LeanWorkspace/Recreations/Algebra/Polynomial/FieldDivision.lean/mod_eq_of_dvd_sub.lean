import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Field R] {p q : R[X]}

private theorem quotient_mul_add_remainder_eq_aux (p q : R[X]) : q * Polynomial.div p q + Polynomial.mod p q = p := by
  by_cases h : q = 0
  · simp only [h, zero_mul, Polynomial.mod, modByMonic_zero, zero_add]
  · conv =>
      rhs
      rw [← modByMonic_add_div p (q * Polynomial.C q.leadingCoeff⁻¹)]
    rw [Polynomial.div, Polynomial.mod, add_comm, mul_assoc]


private theorem remainder_lt_aux (p : R[X]) (hq : q ≠ 0) : degree (Polynomial.mod p q) < degree q := by
  rw [← degree_mul_leadingCoeff_inv q hq]
  exact degree_modByMonic_lt p (monic_mul_leadingCoeff_inv hq)


theorem mod_eq_of_dvd_sub {p₁ p₂ q : R[X]} (h : q ∣ p₁ - p₂) : p₁ % q = p₂ % q := by
  obtain rfl | hq := eq_or_ne q 0
  · simpa [sub_eq_zero] using h
  simp_rw [Polynomial.mod_def]
  apply Polynomial.modByMonic_eq_of_dvd_sub (by simp [Polynomial.Monic.def, hq])
  rw [mul_comm]
  exact (Polynomial.C_mul_dvd (by simpa using hq)).mpr h

