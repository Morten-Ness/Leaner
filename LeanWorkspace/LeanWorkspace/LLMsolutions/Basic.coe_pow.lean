import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

theorem coe_pow (s : Finset α) (n : ℕ) : ↑(s ^ n) = (s : Set α) ^ n := by
  induction n with
  | zero =>
      ext x
      simp
  | succ n ih =>
      ext x
      simp [pow_succ, ih]
