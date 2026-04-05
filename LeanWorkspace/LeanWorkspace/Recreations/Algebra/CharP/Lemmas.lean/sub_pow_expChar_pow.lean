import Mathlib

variable {R S : Type*}

variable [CommRing R] (x y : R) (n : ℕ) {p : ℕ}

variable [hR : ExpChar R p]

theorem sub_pow_expChar_pow : (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n := sub_pow_expChar_pow_of_commute _ _ <| .all ..

