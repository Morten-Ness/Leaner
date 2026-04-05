import Mathlib

variable {G M S : Type*}

variable [Monoid M] {a b : M}

theorem pow_pow_self (a : M) (m n : ℕ) : Commute (a ^ m) (a ^ n) := Commute.pow_pow (Commute.refl a) m n

