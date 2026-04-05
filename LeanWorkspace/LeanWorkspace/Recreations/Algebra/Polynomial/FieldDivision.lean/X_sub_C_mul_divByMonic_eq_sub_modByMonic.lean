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


theorem X_sub_C_mul_divByMonic_eq_sub_modByMonic {K : Type*} [Ring K] (f : K[X]) (a : K) :
    (Polynomial.X - Polynomial.C a) * (f /ₘ (Polynomial.X - Polynomial.C a)) = f - f %ₘ (Polynomial.X - Polynomial.C a) := by
  rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', modByMonic_eq_sub_mul_div]

