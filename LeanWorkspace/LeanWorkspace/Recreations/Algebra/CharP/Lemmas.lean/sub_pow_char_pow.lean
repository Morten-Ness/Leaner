import Mathlib

variable {R S : Type*}

variable [CommRing R] (x y : R) (n : ℕ) {p : ℕ}

variable [hp : Fact p.Prime] [CharP R p]

theorem sub_pow_char_pow : (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n := sub_pow_expChar_pow ..

