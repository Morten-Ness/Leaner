import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R]

theorem eval_iterate_derivative_rootMultiplicity {p : R[X]} {t : R} :
    (derivative^[p.rootMultiplicity t] p).eval t =
      (p.rootMultiplicity t).factorial • (p /ₘ (Polynomial.X - Polynomial.C t) ^ p.rootMultiplicity t).eval t := by
  set m := p.rootMultiplicity t with hm
  conv_lhs => rw [← p.pow_mul_divByMonic_rootMultiplicity_eq t, ← hm]
  rw [iterate_derivative_mul, eval_finset_sum, sum_eq_single_of_mem _ (mem_range.mpr m.succ_pos)]
  · rw [m.choose_zero_right, one_smul, eval_mul, m.sub_zero, iterate_derivative_X_sub_pow_self,
      eval_natCast, nsmul_eq_mul]; rfl
  · intro b hb hb0
    rw [iterate_derivative_X_sub_pow, eval_smul, eval_mul, eval_smul, eval_pow,
      Nat.sub_sub_self (mem_range_succ_iff.mp hb), eval_sub, eval_X, eval_C, sub_self,
      zero_pow hb0, smul_zero, zero_mul, smul_zero]

