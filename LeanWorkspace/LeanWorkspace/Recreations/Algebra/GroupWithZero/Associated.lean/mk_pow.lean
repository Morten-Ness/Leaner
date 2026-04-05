import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem mk_pow (a : M) (n : ℕ) : Associates.mk (a ^ n) = Associates.mk a ^ n := by
  induction n <;> simp [*, pow_succ, Associates.Associated.symm Associates.mk_mul_mk]

