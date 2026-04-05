import Mathlib

variable {G M S : Type*}

variable [Monoid M] {a b : M}

theorem pow_self (a : M) (n : ℕ) : Commute (a ^ n) a := Commute.pow_left (Commute.refl a) n

