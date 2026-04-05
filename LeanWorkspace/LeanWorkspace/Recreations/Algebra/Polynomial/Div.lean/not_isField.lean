import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem not_isField : ¬IsField R[X] := by
  nontriviality R
  intro h
  letI := h.toField
  simpa using congr_arg natDegree (monic_X.eq_one_of_isUnit <| monic_X (R := R).ne_zero.isUnit)

