import Mathlib

variable {α M : Type*} {n : ℕ}

variable [Zero α]

theorem cons_nonzero_iff {v : Fin n → α} {x : α} : vecCons x v ≠ 0 ↔ x ≠ 0 ∨ v ≠ 0 where
  mp h := not_and_or.mp (h ∘ cons_eq_zero_iff.mpr)
  mpr h := mt cons_eq_zero_iff.mp (not_and_or.mpr h)

