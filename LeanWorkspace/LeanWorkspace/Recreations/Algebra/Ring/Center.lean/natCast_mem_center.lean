import Mathlib

variable {M : Type*}

theorem natCast_mem_center [NonAssocSemiring M] (n : ℕ) : (n : M) ∈ Set.center M where
  comm _ := by rw [commute_iff_eq, Nat.commute_cast]
  left_assoc _ _ := by
    induction n with
    | zero => rw [Nat.cast_zero, zero_mul, zero_mul, zero_mul]
    | succ n ihn => rw [Nat.cast_succ, add_mul, one_mul, ihn, add_mul, add_mul, one_mul]
  right_assoc _ _ := by
    induction n with
    | zero => rw [Nat.cast_zero, mul_zero, mul_zero, mul_zero]
    | succ n ihn => rw [Nat.cast_succ, mul_add, ihn, mul_add, mul_add, mul_one, mul_one]

