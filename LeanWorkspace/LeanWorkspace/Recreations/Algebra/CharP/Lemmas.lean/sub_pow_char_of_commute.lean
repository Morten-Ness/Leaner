import Mathlib

variable {R S : Type*}

variable [Ring R] {x y : R} (p n : ℕ)

variable [hp : Fact p.Prime] [CharP R p]

theorem sub_pow_char_of_commute (h : Commute x y) : (x - y) ^ p = x ^ p - y ^ p := sub_pow_expChar_of_commute _ h

