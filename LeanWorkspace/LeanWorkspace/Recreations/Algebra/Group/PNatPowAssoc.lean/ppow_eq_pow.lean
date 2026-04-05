import Mathlib

variable {M : Type*}

theorem ppow_eq_pow [Monoid M] [Pow M ℕ+] [PNatPowAssoc M] (x : M) (n : ℕ+) :
    x ^ n = x ^ (n : ℕ) := by
  induction n with
  | one => rw [ppow_one, PNat.one_coe, pow_one]
  | succ k hk => rw [ppow_add, ppow_one, PNat.add_coe, pow_add, PNat.one_coe, pow_one, ← hk]

