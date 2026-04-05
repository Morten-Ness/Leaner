import Mathlib

variable {R S : Type*}

variable [CommSemiring R] (x y : R) (p n : ℕ)

variable [hR : ExpChar R p]

theorem add_pow_expChar : (x + y) ^ p = x ^ p + y ^ p := add_pow_expChar_of_commute _ <| .all ..

