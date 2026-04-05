import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M]

variable {p : M} (hp : Prime p)

theorem ne_one : p ≠ 1 := fun h => hp.2.1 (h.symm ▸ isUnit_one)

