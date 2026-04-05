import Mathlib

open scoped Polynomial

variable (p q : ℤ[X])

theorem isUnitTrinomial_iff :
    p.IsUnitTrinomial ↔ #p.support = 3 ∧ ∀ k ∈ p.support, IsUnit (p.coeff k) := by
  refine ⟨fun hp => ⟨Polynomial.IsUnitTrinomial.card_support_eq_three hp, fun k => Polynomial.IsUnitTrinomial.coeff_isUnit hp⟩, fun hp => ?_⟩
  obtain ⟨k, m, n, hkm, hmn, x, y, z, hx, hy, hz, rfl⟩ := Polynomial.IsUnitTrinomial.card_support_eq_three.mp hp.1
  rw [support_trinomial hkm hmn hx hy hz] at hp
  replace hx := hp.2 k (mem_insert_self k {m, n})
  replace hy := hp.2 m (mem_insert_of_mem (mem_insert_self m {n}))
  replace hz := hp.2 n (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self n)))
  simp_rw [coeff_add, coeff_C_mul, coeff_X_pow_self, mul_one, coeff_X_pow] at hx hy hz
  rw [if_neg hkm.ne, if_neg (hkm.trans hmn).ne] at hx
  rw [if_neg hkm.ne', if_neg hmn.ne] at hy
  rw [if_neg (hkm.trans hmn).ne', if_neg hmn.ne'] at hz
  simp_rw [mul_zero, zero_add, add_zero] at hx hy hz
  exact ⟨k, m, n, hkm, hmn, hx.unit, hy.unit, hz.unit, rfl⟩

