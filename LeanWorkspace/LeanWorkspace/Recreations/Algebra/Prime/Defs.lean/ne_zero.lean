import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M]

variable {p : M} (hp : Prime p)

theorem ne_zero : p ≠ 0 := hp.1

