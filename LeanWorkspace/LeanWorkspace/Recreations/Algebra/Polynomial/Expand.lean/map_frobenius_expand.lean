import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

variable [ExpChar R p]

theorem map_frobenius_expand (f : R[X]) : map (frobenius R p) (Polynomial.expand R p f) = f ^ p := by
  refine f.induction_on' (fun a b ha hb => ?_) fun n a => ?_
  · rw [map_add, Polynomial.map_add, ha, hb, add_pow_expChar]
  · rw [Polynomial.expand_monomial, map_monomial, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial,
      mul_pow, ← Polynomial.C.map_pow, frobenius_def]
    ring

