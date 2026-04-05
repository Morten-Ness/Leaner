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


theorem map_mod [Field k] (f : R →+* k) : (p % q).map f = p.map f % q.map f := by
  by_cases hq0 : q = 0
  · simp [hq0]
  · rw [Polynomial.mod_def, Polynomial.mod_def, Polynomial.leadingCoeff_map f, ← map_inv₀ f, ← map_C f, ← Polynomial.map_mul f,
      map_modByMonic f (monic_mul_leadingCoeff_inv hq0)]

