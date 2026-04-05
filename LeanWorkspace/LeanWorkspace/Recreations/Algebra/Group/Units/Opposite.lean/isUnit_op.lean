import Mathlib

variable {α : Type*}

theorem isUnit_op {M} [Monoid M] {m : M} : IsUnit (op m) ↔ IsUnit m := ⟨IsUnit.unop, IsUnit.op⟩

