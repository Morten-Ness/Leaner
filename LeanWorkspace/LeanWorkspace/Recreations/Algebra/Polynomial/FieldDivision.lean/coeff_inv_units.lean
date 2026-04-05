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


theorem coeff_inv_units (u : R[X]ˣ) (n : ℕ) : ((↑u : R[X]).coeff n)⁻¹ = (↑u⁻¹ : R[X]).coeff n := by
  rw [eq_C_of_degree_eq_zero (degree_coe_units u), eq_C_of_degree_eq_zero (degree_coe_units u⁻¹),
    coeff_C, coeff_C, inv_eq_one_div]
  split_ifs
  · rw [div_eq_iff_mul_eq (coeff_coe_units_zero_ne_zero u), coeff_zero_eq_eval_zero,
        coeff_zero_eq_eval_zero, ← eval_mul, ← Units.val_mul, inv_mul_cancel]
    simp
  · simp

