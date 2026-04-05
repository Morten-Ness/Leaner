import Mathlib

variable {R S : Type*}

variable [CommRing R] (x y : R) (n : ℕ) {p : ℕ}

variable [hR : ExpChar R p]

theorem sub_pow_expChar : (x - y) ^ p = x ^ p - y ^ p := sub_pow_expChar_of_commute _ <| .all ..

