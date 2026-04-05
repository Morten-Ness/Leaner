import Mathlib

open scoped Polynomial

variable {Fq : Type*} [Field Fq] [Fintype Fq]

theorem cardPowDegree_isEuclidean : IsEuclidean (Polynomial.cardPowDegree : AbsoluteValue Fq[X] ℤ) := have card_pos : 0 < Fintype.card Fq := Fintype.card_pos_iff.mpr inferInstance
  have pow_pos : ∀ n, 0 < (Fintype.card Fq : ℤ) ^ n := fun n =>
    pow_pos (Int.natCast_pos.mpr card_pos) n
  { map_lt_map_iff' := fun {p q} => by
      classical
      change Polynomial.cardPowDegree p < Polynomial.cardPowDegree q ↔ degree p < degree q
      simp only [Polynomial.cardPowDegree_apply]
      split_ifs with hp hq hq
      · simp only [hp, hq, lt_self_iff_false]
      · simp only [hp, hq, degree_zero, Ne, bot_lt_iff_ne_bot, degree_eq_bot, pow_pos,
          not_false_iff]
      · simp only [hq, degree_zero, not_lt_bot, (pow_pos _).not_gt]
      · rw [degree_eq_natDegree hp, degree_eq_natDegree hq, Nat.cast_lt, pow_lt_pow_iff_right₀]
        exact mod_cast @Fintype.one_lt_card Fq _ _ }

