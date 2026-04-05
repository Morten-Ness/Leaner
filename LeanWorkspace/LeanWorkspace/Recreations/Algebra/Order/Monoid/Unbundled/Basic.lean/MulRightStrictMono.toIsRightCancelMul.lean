import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [LinearOrder α] {a b c d : α}

theorem MulRightStrictMono.toIsRightCancelMul [MulRightStrictMono α] : IsRightCancelMul α where
  mul_right_cancel _ _ _ h := mul_left_strictMono.injective h

