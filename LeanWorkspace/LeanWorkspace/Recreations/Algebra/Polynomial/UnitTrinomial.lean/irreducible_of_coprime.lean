import Mathlib

open scoped Polynomial

variable (p q : ℤ[X])

theorem irreducible_of_coprime (hp : p.IsUnitTrinomial)
    (h : IsRelPrime p p.mirror) : Irreducible p := by
  refine irreducible_of_mirror Polynomial.IsUnitTrinomial.not_isUnit hp (fun q hpq => ?_) h
  have hq : Polynomial.IsUnitTrinomial q := (Polynomial.isUnitTrinomial_iff'' hpq).mp hp
  obtain ⟨k, m, n, hkm, hmn, u, v, w, hp⟩ := hp
  obtain ⟨k', m', n', hkm', hmn', x, y, z, hq⟩ := hq
  have hk : k = k' := by
    rw [← mul_right_inj' (show 2 ≠ 0 from two_ne_zero), ←
      Polynomial.trinomial_natTrailingDegree hkm hmn Polynomial.IsUnitTrinomial.ne_zero u, ← hp, ← natTrailingDegree_mul_mirror, hpq,
      natTrailingDegree_mul_mirror, hq, Polynomial.trinomial_natTrailingDegree hkm' hmn' Polynomial.IsUnitTrinomial.ne_zero x]
  have hn : n = n' := by
    rw [← mul_right_inj' (show 2 ≠ 0 from two_ne_zero), ← Polynomial.trinomial_natDegree hkm hmn Polynomial.IsUnitTrinomial.ne_zero w, ←
      hp, ← natDegree_mul_mirror, hpq, natDegree_mul_mirror, hq,
      Polynomial.trinomial_natDegree hkm' hmn' Polynomial.IsUnitTrinomial.ne_zero z]
  subst hk
  subst hn
  rcases eq_or_eq_neg_of_sq_eq_sq (y : ℤ) (v : ℤ)
      ((Int.isUnit_sq y.isUnit).trans (Int.isUnit_sq v.isUnit).symm) with
    (h1 | h1)
  · rw [h1] at hq
    rcases Polynomial.IsUnitTrinomial.irreducible_aux3 hkm hmn hkm' hmn' u v w x z hp hq hpq with (h2 | h2)
    · exact Or.inl h2
    · exact Or.inr (Or.inr (Or.inl h2))
  · rw [h1] at hq
    rw [Polynomial.trinomial_def] at hp
    rw [← neg_inj, neg_add, neg_add, ← neg_mul, ← neg_mul, ← neg_mul, ← C_neg, ← C_neg, ← C_neg]
      at hp
    rw [← neg_mul_neg, ← mirror_neg] at hpq
    rcases Polynomial.IsUnitTrinomial.irreducible_aux3 hkm hmn hkm' hmn' (-u) (-v) (-w) x z hp hq hpq with (rfl | rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inr p.mirror_neg))

