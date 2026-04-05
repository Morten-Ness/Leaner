import Mathlib

variable {α : Type*}

theorem isUnit_unop {M} [Monoid M] {m : Mᵐᵒᵖ} : IsUnit (unop m) ↔ IsUnit m := ⟨IsUnit.op, IsUnit.unop⟩

