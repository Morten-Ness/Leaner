import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M]

theorem not_prime_zero : ¬Prime (0 : M) := fun h => Prime.ne_zero h rfl

