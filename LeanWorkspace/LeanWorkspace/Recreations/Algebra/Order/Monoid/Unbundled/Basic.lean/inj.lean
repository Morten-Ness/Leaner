import Mathlib

variable {α β : Type*}

theorem inj [Mul α] [PartialOrder α] {a b c : α} (ha : MulLECancellable a) :
    a * b = a * c ↔ b = c := MulLECancellable.Injective ha.eq_iff

