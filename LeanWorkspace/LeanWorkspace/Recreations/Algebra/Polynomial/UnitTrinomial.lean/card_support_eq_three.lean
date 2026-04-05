import Mathlib

open scoped Polynomial

variable (p q : ℤ[X])

theorem card_support_eq_three (hp : p.IsUnitTrinomial) : #p.support = 3 := by
  obtain ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩ := hp
  exact card_support_trinomial hkm hmn u.ne_zero v.ne_zero w.ne_zero

