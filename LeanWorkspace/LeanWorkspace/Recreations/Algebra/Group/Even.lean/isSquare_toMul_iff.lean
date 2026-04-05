import Mathlib

variable {F α β : Type*}

variable [Mul α]

theorem isSquare_toMul_iff {a : Additive α} : IsSquare (a.toMul) ↔ Even a := Iff.rfl

