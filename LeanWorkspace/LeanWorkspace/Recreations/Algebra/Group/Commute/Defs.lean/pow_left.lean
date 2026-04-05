import Mathlib

variable {G M S : Type*}

variable [Monoid M] {a b : M}

theorem pow_left (h : Commute a b) (n : ℕ) : Commute (a ^ n) b := Commute.symm (Commute.pow_right h.symm n)

-- todo: should nat power be called `nsmul` here?

