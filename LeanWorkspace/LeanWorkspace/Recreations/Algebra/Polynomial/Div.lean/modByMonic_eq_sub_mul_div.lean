import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem modByMonic_eq_sub_mul_div :
    ∀ p q : R[X], p %ₘ q = p - q * (p /ₘ q)
  | p, q =>
    letI := Classical.decEq R
    if hq : q.Monic then
      if h : degree q ≤ degree p ∧ p ≠ 0 then by
        have _wf := Polynomial.div_wf_lemma h hq
        have ih := modByMonic_eq_sub_mul_div
          (p - q * (Polynomial.C (leadingCoeff p) * Polynomial.X ^ (natDegree p - natDegree q))) q
        unfold Polynomial.modByMonic Polynomial.divByMonic Polynomial.divModByMonicAux
        rw [dif_pos hq, dif_pos h]
        rw [Polynomial.modByMonic, dif_pos hq] at ih
        refine ih.trans ?_
        rw [Polynomial.divByMonic, dif_pos hq, dif_pos hq, dif_pos h, mul_add, sub_add_eq_sub_sub]
      else by
        unfold Polynomial.modByMonic Polynomial.divByMonic Polynomial.divModByMonicAux
        dsimp
        rw [dif_pos hq, if_neg h, dif_pos hq, if_neg h, mul_zero, sub_zero]
    else by
      rw [Polynomial.modByMonic_eq_of_not_monic _ hq, Polynomial.divByMonic_eq_of_not_monic _ hq, mul_zero, sub_zero]
  termination_by p => p

