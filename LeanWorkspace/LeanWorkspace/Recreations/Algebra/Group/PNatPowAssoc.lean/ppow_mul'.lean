import Mathlib

variable {M : Type*}

variable [Mul M] [Pow M ℕ+] [PNatPowAssoc M]

theorem ppow_mul' (x : M) (m n : ℕ+) : x ^ (m * n) = (x ^ n) ^ m := by
  rw [mul_comm]
  exact ppow_mul x n m

