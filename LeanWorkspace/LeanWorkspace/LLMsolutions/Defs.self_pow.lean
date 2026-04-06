import Mathlib

variable {G M S : Type*}

variable [Monoid M] {a b : M}

theorem self_pow (a : M) (n : ℕ) : Commute a (a ^ n) := by
  exact Commute.self_pow a n
