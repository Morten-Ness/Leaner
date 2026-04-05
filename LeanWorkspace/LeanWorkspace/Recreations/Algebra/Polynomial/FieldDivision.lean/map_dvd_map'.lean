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


theorem map_dvd_map' [Field k] (f : R →+* k) {x y : R[X]} : x.map f ∣ y.map f ↔ x ∣ y := by
  by_cases H : x = 0
  · rw [H, Polynomial.map_zero, zero_dvd_iff, zero_dvd_iff, Polynomial.map_eq_zero]
  · classical
    rw [← normalize_dvd_iff, ← @normalize_dvd_iff R[X], normalize_apply, normalize_apply,
      Polynomial.coe_normUnit_of_ne_zero H, Polynomial.coe_normUnit_of_ne_zero (mt (Polynomial.map_eq_zero f).1 H),
      Polynomial.leadingCoeff_map, ← map_inv₀ f, ← map_C, ← Polynomial.map_mul,
      map_dvd_map _ f.injective (monic_mul_leadingCoeff_inv H)]

