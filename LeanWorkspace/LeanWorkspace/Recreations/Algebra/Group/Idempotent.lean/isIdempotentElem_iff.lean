import Mathlib

variable {M N S : Type*}

theorem isIdempotentElem_iff [Mul M] {a : M} : IsIdempotentElem a ↔ a * a = a := Iff.rfl

