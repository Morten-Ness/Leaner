import Mathlib

variable {M N S : Type*}

variable [MulOneClass M] {a : M}

theorem one : IsIdempotentElem (1 : M) := mul_one _

