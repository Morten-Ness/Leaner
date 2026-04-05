import Mathlib

section

variable {M : Type*}

theorem ppow_eq_pow [Monoid M] [Pow M ℕ+] [PNatPowAssoc M] (x : M) (n : ℕ+) :
    x ^ n = x ^ (n : ℕ) := by
  induction n with
  | one => rw [ppow_one, PNat.one_coe, pow_one]
  | succ k hk => rw [ppow_add, ppow_one, PNat.add_coe, pow_add, PNat.one_coe, pow_one, ← hk]

end

section

variable {M : Type*}

variable [Mul M] [Pow M ℕ+] [PNatPowAssoc M]

theorem ppow_mul' (x : M) (m n : ℕ+) : x ^ (m * n) = (x ^ n) ^ m := by
  rw [mul_comm]
  exact ppow_mul x n m

end

section

variable {M : Type*}

variable [Mul M] [Pow M ℕ+] [PNatPowAssoc M]

theorem ppow_mul (x : M) (m n : ℕ+) : x ^ (m * n) = (x ^ m) ^ n := by
  induction n with
  | one => rw [ppow_one, mul_one]
  | succ k hk => rw [ppow_add, ppow_one, mul_add, ppow_add, mul_one, hk]

end

section

variable {M : Type*}

variable [Mul M] [Pow M ℕ+] [PNatPowAssoc M]

theorem ppow_mul_assoc (k m n : ℕ+) (x : M) :
    (x ^ k * x ^ m) * x ^ n = x ^ k * (x ^ m * x ^ n) := by
  simp only [← ppow_add, add_assoc]

end

section

variable {M : Type*}

variable [Mul M] [Pow M ℕ+] [PNatPowAssoc M]

theorem ppow_mul_comm (m n : ℕ+) (x : M) :
    x ^ m * x ^ n = x ^ n * x ^ m := by simp only [← ppow_add, add_comm]

end
