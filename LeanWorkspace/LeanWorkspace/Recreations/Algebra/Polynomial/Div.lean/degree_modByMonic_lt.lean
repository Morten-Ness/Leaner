import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem degree_modByMonic_lt [Nontrivial R] :
    ∀ (p : R[X]) {q : R[X]} (_hq : Polynomial.Monic q), degree (p %ₘ q) < degree q
  | p, q, hq =>
    letI := Classical.decEq R
    if h : degree q ≤ degree p ∧ p ≠ 0 then by
      have _wf := Polynomial.div_wf_lemma ⟨h.1, h.2⟩ hq
      have :=
        degree_modByMonic_lt (p - q * (Polynomial.C (leadingCoeff p) * Polynomial.X ^ (natDegree p - natDegree q))) hq
      grind [Polynomial.divModByMonicAux, Polynomial.modByMonic]
    else
      Or.casesOn (not_and_or.1 h)
        (by
          unfold Polynomial.modByMonic Polynomial.divModByMonicAux
          dsimp
          rw [dif_pos hq, if_neg h]
          exact lt_of_not_ge)
        (by
          intro hp
          unfold Polynomial.modByMonic Polynomial.divModByMonicAux
          dsimp
          rw [dif_pos hq, if_neg h, Classical.not_not.1 hp]
          exact lt_of_le_of_ne bot_le (Ne.symm (mt degree_eq_bot.1 hq.ne_zero)))
  termination_by p => p

