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


theorem X_sub_C_dvd_derivative_of_X_sub_C_dvd_divByMonic {K : Type*} [Field K] (f : K[X]) {a : K}
    (hf : (Polynomial.X - Polynomial.C a) ∣ f /ₘ (Polynomial.X - Polynomial.C a)) : Polynomial.X - Polynomial.C a ∣ derivative f := by
  have key := Polynomial.divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative f a
  have ⟨u,hu⟩ := hf
  rw [← key, hu, ← mul_add (Polynomial.X - Polynomial.C a) u _]
  use (u + derivative ((Polynomial.X - Polynomial.C a) * u))

