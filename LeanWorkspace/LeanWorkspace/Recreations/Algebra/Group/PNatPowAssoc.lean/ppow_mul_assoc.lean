import Mathlib

variable {M : Type*}

variable [Mul M] [Pow M ℕ+] [PNatPowAssoc M]

theorem ppow_mul_assoc (k m n : ℕ+) (x : M) :
    (x ^ k * x ^ m) * x ^ n = x ^ k * (x ^ m * x ^ n) := by
  simp only [← ppow_add, add_assoc]

