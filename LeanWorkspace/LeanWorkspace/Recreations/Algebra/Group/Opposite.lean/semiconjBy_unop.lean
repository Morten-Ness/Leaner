import Mathlib

variable {α : Type*}

theorem semiconjBy_unop [Mul α] {a x y : αᵐᵒᵖ} :
    SemiconjBy (unop a) (unop y) (unop x) ↔ SemiconjBy a x y := by
  conv_rhs => rw [← op_unop a, ← op_unop x, ← op_unop y, MulOpposite.semiconjBy_op]

attribute [nolint simpComm] AddOpposite.addSemiconjBy_unop

