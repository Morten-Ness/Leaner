import Mathlib

variable (R : Type*)

variable [AddMonoidWithOne R]

theorem expChar_pow_pos (q : ℕ) [ExpChar R q] (n : ℕ) : 0 < q ^ n := Nat.pow_pos (expChar_pos R q)

