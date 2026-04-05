import Mathlib

section

variable {α : Type*}

theorem commute_unop [Mul α] {x y : αᵐᵒᵖ} : Commute (unop x) (unop y) ↔ Commute x y := MulOpposite.semiconjBy_unop

attribute [nolint simpComm] AddOpposite.addCommute_unop

end

section

variable {α : Type*}

theorem semiconjBy_op [Mul α] {a x y : α} : SemiconjBy (op a) (op y) (op x) ↔ SemiconjBy a x y := by
  simp only [SemiconjBy, ← op_mul, op_inj, eq_comm]

end

section

variable {α : Type*}

theorem semiconjBy_unop [Mul α] {a x y : αᵐᵒᵖ} :
    SemiconjBy (unop a) (unop y) (unop x) ↔ SemiconjBy a x y := by
  conv_rhs => rw [← op_unop a, ← op_unop x, ← op_unop y, MulOpposite.semiconjBy_op]

attribute [nolint simpComm] AddOpposite.addSemiconjBy_unop

end
