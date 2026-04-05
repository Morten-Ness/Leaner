import Mathlib

variable {F α β : Type*}

variable [Mul α]

theorem even_ofMul_iff {a : α} : Even (Additive.ofMul a) ↔ IsSquare a := Iff.rfl

