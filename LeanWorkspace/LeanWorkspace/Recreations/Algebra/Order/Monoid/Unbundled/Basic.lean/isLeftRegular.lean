import Mathlib

variable {α β : Type*}

theorem isLeftRegular [Mul α] [PartialOrder α] {a : α}
    (ha : MulLECancellable a) : IsLeftRegular a := MulLECancellable.Injective ha

