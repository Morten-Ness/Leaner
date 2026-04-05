import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem degree_divByMonic_lt (p q : R[X]) (hp0 : p ≠ 0)
    (h0q : 0 < degree q) : degree (p /ₘ q) < degree p := letI := Classical.decEq R
  if hq : q.Monic then
    if hpq : degree p < degree q then by
      haveI := Nontrivial.of_polynomial_ne hp0
      rw [(Polynomial.divByMonic_eq_zero_iff hq).2 hpq, degree_eq_natDegree hp0]
      exact WithBot.bot_lt_coe _
    else by
      haveI := Nontrivial.of_polynomial_ne hp0
      rw [← Polynomial.degree_add_divByMonic hq (not_lt.1 hpq), degree_eq_natDegree hq.ne_zero,
        degree_eq_natDegree (mt (Polynomial.divByMonic_eq_zero_iff hq).1 hpq)]
      exact
        Nat.cast_lt.2
          (Nat.lt_add_of_pos_left (Nat.cast_lt.1 <|
            by simpa [degree_eq_natDegree hq.ne_zero] using h0q))
  else by
    rwa [Polynomial.divByMonic_eq_of_not_monic _ hq, degree_zero, bot_lt_iff_ne_bot, degree_ne_bot]

