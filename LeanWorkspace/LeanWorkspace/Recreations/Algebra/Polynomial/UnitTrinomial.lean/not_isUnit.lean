import Mathlib

open scoped Polynomial

variable (p q : ℤ[X])

theorem not_isUnit (hp : p.IsUnitTrinomial) : ¬IsUnit p := by
  obtain ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩ := hp
  exact fun h =>
    ne_zero_of_lt hmn
      ((Polynomial.trinomial_natDegree hkm hmn w.ne_zero).symm.trans
        (natDegree_eq_of_degree_eq_some (degree_eq_zero_of_isUnit h)))

