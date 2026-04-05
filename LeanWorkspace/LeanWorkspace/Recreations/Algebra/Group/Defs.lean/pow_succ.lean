import Mathlib

variable {G : Type*}

variable {M : Type*} [Monoid M] {a b c : M}

theorem pow_succ (a : M) (n : ℕ) : a ^ (n + 1) = a ^ n * a := Monoid.npow_succ n a

