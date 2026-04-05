import Mathlib

variable {R S : Type*}

variable [CommRing R] (x y : R) (n : ℕ) {p : ℕ}

variable [hp : Fact p.Prime] [CharP R p]

theorem sub_pow_char : (x - y) ^ p = x ^ p - y ^ p := sub_pow_expChar ..

