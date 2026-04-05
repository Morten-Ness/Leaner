import Mathlib

open scoped Ring

variable {R : Type*}

theorem pos_of_invertible_cast [NonAssocSemiring R] [Nontrivial R] (n : ℕ) [Invertible (n : R)] :
    0 < n := Nat.zero_lt_of_ne_zero fun h => Invertible.ne_zero (n : R) (h ▸ Nat.cast_zero)

