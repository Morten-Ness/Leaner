import Mathlib

variable {R S : Type*}

variable [Ring R] {x y : R} (p n : ℕ)

variable [hR : ExpChar R p]

theorem sub_pow_eq_mul_pow_sub_pow_div_expChar_of_commute (h : Commute x y) :
    (x - y) ^ n = (x - y) ^ (n % p) * (x ^ p - y ^ p) ^ (n / p) := by
  rw [← sub_pow_expChar_of_commute _ h, ← pow_mul, ← pow_add, Nat.mod_add_div]

