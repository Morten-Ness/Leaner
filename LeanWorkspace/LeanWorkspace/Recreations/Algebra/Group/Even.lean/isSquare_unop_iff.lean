import Mathlib

variable {F α β : Type*}

variable [Mul α]

theorem isSquare_unop_iff {a : αᵐᵒᵖ} : IsSquare (unop a) ↔ IsSquare a := isSquare_op_iff.symm

