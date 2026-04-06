import Mathlib

variable {M N S : Type*}

variable [Monoid M] {a : M}

theorem pow_succ_eq (n : ℕ) (h : IsIdempotentElem a) : a ^ (n + 1) = a := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, ih, h.eq]
