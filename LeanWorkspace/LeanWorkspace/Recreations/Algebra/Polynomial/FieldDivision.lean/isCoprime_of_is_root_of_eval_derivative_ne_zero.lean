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


theorem isCoprime_of_is_root_of_eval_derivative_ne_zero {K : Type*} [Field K] (f : K[X]) (a : K)
    (hf' : f.derivative.eval a ≠ 0) : IsCoprime (Polynomial.X - Polynomial.C a : K[X]) (f /ₘ (Polynomial.X - Polynomial.C a)) := by
  classical
  refine Or.resolve_left
      (EuclideanDomain.dvd_or_coprime (Polynomial.X - Polynomial.C a) (f /ₘ (Polynomial.X - Polynomial.C a))
        (Polynomial.irreducible_of_degree_eq_one (Polynomial.degree_X_sub_C a))) ?_
  contrapose! hf' with h
  have : Polynomial.X - Polynomial.C a ∣ derivative f := Polynomial.X_sub_C_dvd_derivative_of_X_sub_C_dvd_divByMonic f h
  rw [← modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_sub_C _), modByMonic_X_sub_C_eq_C_eval] at this
  rwa [← C_inj, C_0]

