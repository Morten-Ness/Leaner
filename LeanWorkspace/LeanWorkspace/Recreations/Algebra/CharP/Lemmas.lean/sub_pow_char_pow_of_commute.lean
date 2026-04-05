import Mathlib

variable {R S : Type*}

variable [Ring R] {x y : R} (p n : ℕ)

variable [hp : Fact p.Prime] [CharP R p]

theorem sub_pow_char_pow_of_commute (h : Commute x y) : (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n := sub_pow_expChar_pow_of_commute _ _ h

