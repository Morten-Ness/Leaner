import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem reflect_mul_induction (cf cg : ℕ) (N O : ℕ) (f g : R[X]) (Cf : #f.support ≤ cf.succ)
    (Cg : #g.support ≤ cg.succ) (Nf : f.natDegree ≤ N) (Og : g.natDegree ≤ O) :
    Polynomial.reflect (N + O) (f * g) = Polynomial.reflect N f * Polynomial.reflect O g := by
  induction cf generalizing f with
  | zero =>
    induction cg generalizing g with
    | zero =>
      rw [← C_mul_X_pow_eq_self Cf, ← C_mul_X_pow_eq_self Cg]
      simp_rw [mul_assoc, X_pow_mul, mul_assoc, ← pow_add (X : R[X]), Polynomial.reflect_C_mul,
        Polynomial.reflect_monomial, add_comm, Polynomial.revAt_add Nf Og, mul_assoc, X_pow_mul, mul_assoc, ←
        pow_add (X : R[X]), add_comm]
    | succ cg hcg =>
      by_cases g0 : g = 0
      · rw [g0, Polynomial.reflect_zero, mul_zero, mul_zero, Polynomial.reflect_zero]
      rw [← eraseLead_add_C_mul_X_pow g, mul_add, Polynomial.reflect_add, Polynomial.reflect_add, mul_add, hcg, hcg] <;>
        try assumption
      · exact le_add_left card_support_C_mul_X_pow_le_one
      · exact le_trans (natDegree_C_mul_X_pow_le g.leadingCoeff g.natDegree) Og
      · exact Nat.lt_succ_iff.mp (lt_of_lt_of_le (eraseLead_support_card_lt g0) Cg)
      · exact le_trans eraseLead_natDegree_le_aux Og
  | succ cf hcf =>
    by_cases f0 : f = 0
    · rw [f0, Polynomial.reflect_zero, zero_mul, zero_mul, Polynomial.reflect_zero]
    rw [← eraseLead_add_C_mul_X_pow f, add_mul, Polynomial.reflect_add, Polynomial.reflect_add, add_mul, hcf, hcf] <;>
      try assumption
    · exact le_add_left card_support_C_mul_X_pow_le_one
    · exact le_trans (natDegree_C_mul_X_pow_le f.leadingCoeff f.natDegree) Nf
    · exact Nat.lt_succ_iff.mp (lt_of_lt_of_le (eraseLead_support_card_lt f0) Cf)
    · exact le_trans eraseLead_natDegree_le_aux Nf

