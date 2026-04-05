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


theorem div_C_mul : p / (Polynomial.C a * q) = Polynomial.C a⁻¹ * (p / q) := by
  by_cases ha : a = 0
  · simp [ha]
  simp only [Polynomial.div_def, leadingCoeff_mul, mul_inv, leadingCoeff_C, Polynomial.C.map_mul, mul_assoc]
  congr 3
  rw [mul_left_comm q, ← mul_assoc, ← Polynomial.C.map_mul, mul_inv_cancel₀ ha, Polynomial.C.map_one, one_mul]

