import Mathlib

variable {F α β : Type*}

variable [Mul α]

theorem isSquare_op_iff {a : α} : IsSquare (op a) ↔ IsSquare a := ⟨fun ⟨r, hr⟩ ↦ ⟨unop r, congr_arg unop hr⟩, fun ⟨r, hr⟩ ↦ ⟨op r, congr_arg op hr⟩⟩

