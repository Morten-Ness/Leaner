import Mathlib

variable {α β : Type*}

theorem inj_left [Mul α] [@Std.Commutative α (· * ·)] [PartialOrder α] {a b c : α}
    (hc : MulLECancellable c) :
    a * c = b * c ↔ a = b := MulLECancellable.injective_left hc.eq_iff

