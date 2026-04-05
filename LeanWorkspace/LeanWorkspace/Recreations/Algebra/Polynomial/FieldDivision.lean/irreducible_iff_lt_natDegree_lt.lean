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


theorem irreducible_iff_lt_natDegree_lt {p : R[X]} (hp0 : p ≠ 0) (hpu : ¬ IsUnit p) :
    Irreducible p ↔ ∀ q, Polynomial.Monic q → natDegree q ∈ Finset.Ioc 0 (natDegree p / 2) → ¬ q ∣ p := by
  have : p * Polynomial.C (leadingCoeff p)⁻¹ ≠ 1 := by
    contrapose! hpu
    exact .of_mul_eq_one _ hpu
  rw [← irreducible_mul_leadingCoeff_inv,
      (monic_mul_leadingCoeff_inv hp0).irreducible_iff_lt_natDegree_lt this,
      natDegree_mul_leadingCoeff_inv _ hp0]
  simp only [IsUnit.dvd_mul_right
    (isUnit_C.mpr (IsUnit.mk0 (leadingCoeff p)⁻¹ (inv_ne_zero (leadingCoeff_ne_zero.mpr hp0))))]

