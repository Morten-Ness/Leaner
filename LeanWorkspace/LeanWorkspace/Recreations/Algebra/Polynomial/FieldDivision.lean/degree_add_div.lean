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


theorem degree_add_div (hq0 : q ≠ 0) (hpq : degree q ≤ degree p) :
    degree q + degree (p / q) = degree p := by
  have : degree (p % q) < degree (q * (p / q)) :=
    calc
      degree (p % q) < degree q := EuclideanDomain.mod_lt _ hq0
      _ ≤ _ := degree_le_mul_left _ (mt (Polynomial.div_eq_zero_iff hq0).1 (not_lt_of_ge hpq))
  conv_rhs =>
    rw [← EuclideanDomain.div_add_mod p q, degree_add_eq_left_of_degree_lt this, degree_mul]

