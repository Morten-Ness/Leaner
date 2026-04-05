import Mathlib

variable {R S : Type*}

variable {R : Type*} [NonUnitalNonAssocRing R] {r : R}

theorem noZeroDivisors_tfae : List.TFAE
    [NoZeroDivisors R, IsLeftCancelMulZero R, IsRightCancelMulZero R, IsCancelMulZero R] := by
  simp_rw [isLeftCancelMulZero_iff, isRightCancelMulZero_iff, isCancelMulZero_iff_forall_isRegular,
    isLeftRegular_iff_right_eq_zero_of_mul, isRightRegular_iff_left_eq_zero_of_mul,
    isRegular_iff_eq_zero_of_mul]
  tfae_have 1 ↔ 2 := noZeroDivisors_iff_right_eq_zero_of_mul
  tfae_have 1 ↔ 3 := noZeroDivisors_iff_left_eq_zero_of_mul
  tfae_have 1 ↔ 4 := noZeroDivisors_iff_eq_zero_of_mul
  tfae_finish

