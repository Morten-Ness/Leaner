import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M]

theorem not_prime_one : ¬Prime (1 : M) := fun h => Prime.not_unit h isUnit_one

