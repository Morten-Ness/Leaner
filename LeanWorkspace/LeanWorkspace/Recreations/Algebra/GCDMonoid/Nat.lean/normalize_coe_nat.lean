import Mathlib

theorem normalize_coe_nat (n : ℕ) : normalize (n : ℤ) = n := Int.normalize_of_nonneg (ofNat_le_ofNat_of_le <| Nat.zero_le n)

