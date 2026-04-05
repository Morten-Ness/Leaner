import Mathlib

variable {ι M N : Type*}

variable [Monoid M] [Monoid N]

theorem prod_replicate (n : ℕ) (a : M) : (replicate n a).prod = a ^ n := by
  induction n with
  | zero => rw [pow_zero, replicate_zero, prod_nil]
  | succ n ih => rw [replicate_succ, prod_cons, ih, pow_succ']

