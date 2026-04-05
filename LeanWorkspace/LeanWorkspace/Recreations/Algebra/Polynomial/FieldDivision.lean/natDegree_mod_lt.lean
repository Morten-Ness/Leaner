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


theorem natDegree_mod_lt [Field k] (p : k[X]) {q : k[X]} (hq : q.natDegree ≠ 0) :
    (p % q).natDegree < q.natDegree := by
  have hq' : q.leadingCoeff ≠ 0 := by
    rw [leadingCoeff_ne_zero]
    contrapose! hq
    simp [hq]
  rw [Polynomial.mod_def]
  refine (natDegree_modByMonic_lt p ?_ ?_).trans_le ?_
  · refine monic_mul_C_of_leadingCoeff_mul_eq_one ?_
    rw [mul_inv_eq_one₀ hq']
  · contrapose! hq
    rw [← natDegree_mul_C_eq_of_mul_eq_one ((inv_mul_eq_one₀ hq').mpr rfl)]
    simp [hq]
  · exact natDegree_mul_C_le q q.leadingCoeff⁻¹

