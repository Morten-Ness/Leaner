import Mathlib

variable {G : Type*}

variable {M : Type*} [Monoid M] {a b c : M}

theorem npow_eq_pow (n : ℕ) (x : M) : Monoid.npow n x = x ^ n := rfl

