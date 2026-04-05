import Mathlib

open scoped Nat Polynomial

variable {F : Type*} [DivisionSemiring F] {f : F[X]}

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


theorem natDegree_pos (h : Irreducible f) : 0 < f.natDegree := Nat.pos_of_ne_zero fun H ↦ by
  obtain ⟨x, hf⟩ := natDegree_eq_zero.1 H
  by_cases hx : x = 0
  · rw [← hf, hx, map_zero] at h; exact not_irreducible_zero h
  exact h.1 (hf ▸ isUnit_C.2 (Ne.isUnit hx))

