import Mathlib

variable {G : Type*}

variable {M : Type*} [Monoid M] {a b c : M}

theorem pow_zero (a : M) : a ^ 0 = 1 := Monoid.npow_zero _

