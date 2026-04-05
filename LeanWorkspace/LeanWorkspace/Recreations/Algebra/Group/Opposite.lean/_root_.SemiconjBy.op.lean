import Mathlib

variable {α : Type*}

theorem _root_.SemiconjBy.op [Mul α] {a x y : α} (h : SemiconjBy a x y) :
    SemiconjBy (op a) (op y) (op x) := MulOpposite.semiconjBy_op.2 h

