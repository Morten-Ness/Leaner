import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

theorem coe_pow (s : Finset α) (n : ℕ) : ↑(s ^ n) = (s : Set α) ^ n := by
  change ↑(npowRec n s) = (s : Set α) ^ n
  induction n with
  | zero => rw [npowRec, pow_zero, Finset.coe_one]
  | succ n ih => rw [npowRec, pow_succ, Finset.coe_mul, ih]

