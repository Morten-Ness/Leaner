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


theorem leadingCoeff_div (hpq : q.degree ≤ p.degree) :
    (p / q).leadingCoeff = p.leadingCoeff / q.leadingCoeff := by
  by_cases hq : q = 0
  · simp [hq]
  rw [Polynomial.div_def, leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_divByMonic_of_monic (monic_mul_leadingCoeff_inv hq) _, mul_comm,
    div_eq_mul_inv]
  rwa [degree_mul_leadingCoeff_inv q hq]

