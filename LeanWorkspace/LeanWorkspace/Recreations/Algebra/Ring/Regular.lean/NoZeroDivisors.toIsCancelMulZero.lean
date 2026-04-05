import Mathlib

variable {α : Type*}

theorem NoZeroDivisors.toIsCancelMulZero [NonUnitalNonAssocRing α] [NoZeroDivisors α] :
    IsCancelMulZero α where
  mul_left_cancel_of_ne_zero ha := (IsRegular.of_ne_zero' ha).1
  mul_right_cancel_of_ne_zero hb := (IsRegular.of_ne_zero' hb).2

