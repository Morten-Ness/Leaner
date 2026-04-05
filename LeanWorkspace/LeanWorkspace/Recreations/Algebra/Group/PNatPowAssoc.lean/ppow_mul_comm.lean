import Mathlib

variable {M : Type*}

variable [Mul M] [Pow M ℕ+] [PNatPowAssoc M]

theorem ppow_mul_comm (m n : ℕ+) (x : M) :
    x ^ m * x ^ n = x ^ n * x ^ m := by simp only [← ppow_add, add_comm]

