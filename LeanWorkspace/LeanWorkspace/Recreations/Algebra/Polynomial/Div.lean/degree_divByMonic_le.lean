import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem degree_divByMonic_le (p q : R[X]) : degree (p /ₘ q) ≤ degree p := letI := Classical.decEq R
  if hp0 : p = 0 then by simp only [hp0, Polynomial.zero_divByMonic, le_refl]
  else
    if hq : Polynomial.Monic q then
      if h : degree q ≤ degree p then by
        haveI := Nontrivial.of_polynomial_ne hp0
        rw [← Polynomial.degree_add_divByMonic hq h, degree_eq_natDegree hq.ne_zero,
          degree_eq_natDegree (mt (Polynomial.divByMonic_eq_zero_iff hq).1 (not_lt.2 h))]
        exact WithBot.coe_le_coe.2 (Nat.le_add_left _ _)
      else by
        unfold Polynomial.divByMonic Polynomial.divModByMonicAux
        simp [dif_pos hq, h, degree_zero, bot_le]
    else (Polynomial.divByMonic_eq_of_not_monic p hq).symm ▸ bot_le

