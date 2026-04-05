import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem card_support_eraseLead' {c : ℕ} (fc : #f.support = c + 1) :
    #f.eraseLead.support = c := by
  rw [Polynomial.card_support_eraseLead, fc, add_tsub_cancel_right]

