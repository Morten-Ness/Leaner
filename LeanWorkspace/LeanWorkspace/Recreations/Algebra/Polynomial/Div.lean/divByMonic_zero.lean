import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem divByMonic_zero (p : R[X]) : p /ₘ 0 = 0 := letI := Classical.decEq R
  if h : Polynomial.Monic (0 : R[X]) then by
    haveI := monic_zero_iff_subsingleton.mp h
    simp [eq_iff_true_of_subsingleton]
  else by unfold Polynomial.divByMonic Polynomial.divModByMonicAux; rw [dif_neg h]

