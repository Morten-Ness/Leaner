import Mathlib

open scoped Polynomial

variable (p q : ℤ[X])

theorem isUnitTrinomial_iff' :
    p.IsUnitTrinomial ↔
      (p * p.mirror).coeff (((p * p.mirror).natDegree + (p * p.mirror).natTrailingDegree) / 2) =
        3 := by
  rw [natDegree_mul_mirror, natTrailingDegree_mul_mirror, ← mul_add,
    Nat.mul_div_right _ zero_lt_two, coeff_mul_mirror]
  refine ⟨?_, fun hp => ?_⟩
  · rintro ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩
    rw [sum_def, Polynomial.trinomial_support hkm hmn Polynomial.IsUnitTrinomial.ne_zero u Polynomial.IsUnitTrinomial.ne_zero v Polynomial.IsUnitTrinomial.ne_zero w,
      Finset.sum_insert (mt mem_insert.mp (not_or_intro hkm.ne (mt mem_singleton.mp (hkm.trans hmn).ne))),
      Finset.sum_insert (mt mem_singleton.mp hmn.ne), sum_singleton, Polynomial.trinomial_leading_coeff' hkm hmn,
      Polynomial.trinomial_middle_coeff hkm hmn, Polynomial.trinomial_trailing_coeff' hkm hmn]
    simp_rw [← Units.val_pow_eq_pow_val, Int.units_sq, Units.val_one]
    decide
  · have key : ∀ k ∈ p.support, p.coeff k ^ 2 = 1 := fun k hk =>
      Int.sq_eq_one_of_sq_le_three
        ((single_le_sum (fun k _ => sq_nonneg (p.coeff k)) hk).trans hp.le) (mem_support_iff.mp hk)
    refine Polynomial.isUnitTrinomial_iff.mpr ⟨?_, fun k hk => .of_pow_eq_one (key k hk) two_ne_zero⟩
    rw [sum_def, Finset.sum_congr rfl key, Finset.sum_const, Nat.smul_one_eq_cast] at hp
    exact Nat.cast_injective hp

