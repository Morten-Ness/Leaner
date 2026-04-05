import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [LinearOrder α] {a b c d : α}

theorem MulLeftStrictMono.toIsLeftCancelMul [MulLeftStrictMono α] : IsLeftCancelMul α where
  mul_left_cancel _ _ _ h := mul_right_strictMono.injective h

