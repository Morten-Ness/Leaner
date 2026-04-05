import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem natDegree_expand (p : ℕ) (f : R[X]) : (Polynomial.expand R p f).natDegree = f.natDegree * p := by
  rcases p.eq_zero_or_pos with hp | hp
  · rw [hp, Polynomial.coe_expand, pow_zero, mul_zero, ← C_1, eval₂_hom, natDegree_C]
  by_cases hf : f = 0
  · rw [hf, map_zero, natDegree_zero, zero_mul]
  have hf1 : Polynomial.expand R p f ≠ 0 := mt (Polynomial.expand_eq_zero hp).1 hf
  rw [← Nat.cast_inj (R := WithBot ℕ), ← degree_eq_natDegree hf1]
  refine le_antisymm ((degree_le_iff_coeff_zero _ _).2 fun n hn => ?_) ?_
  · rw [Polynomial.coeff_expand hp]
    split_ifs with hpn
    · rw [coeff_eq_zero_of_natDegree_lt]
      contrapose! hn
      norm_cast
      rw [← Nat.div_mul_cancel hpn]
      exact Nat.mul_le_mul_right p hn
    · rfl
  · refine le_degree_of_ne_zero ?_
    rw [Polynomial.coeff_expand_mul hp, ← leadingCoeff]
    exact mt leadingCoeff_eq_zero.1 hf

