import Mathlib

variable {R S : Type*}

variable [CommSemiring R] (x y : R) (p n : ℕ)

variable [hR : ExpChar R p]

theorem add_pow_expChar_pow : (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n := add_pow_expChar_pow_of_commute _ _ <| .all ..

