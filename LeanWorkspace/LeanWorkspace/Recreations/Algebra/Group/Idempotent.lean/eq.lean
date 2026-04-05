import Mathlib

variable {M N S : Type*}

variable [Mul M] {a : M}

theorem eq (ha : IsIdempotentElem a) : a * a = a := ha

