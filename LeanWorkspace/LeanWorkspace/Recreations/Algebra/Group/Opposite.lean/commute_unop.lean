import Mathlib

variable {α : Type*}

theorem commute_unop [Mul α] {x y : αᵐᵒᵖ} : Commute (unop x) (unop y) ↔ Commute x y := MulOpposite.semiconjBy_unop

attribute [nolint simpComm] AddOpposite.addCommute_unop

