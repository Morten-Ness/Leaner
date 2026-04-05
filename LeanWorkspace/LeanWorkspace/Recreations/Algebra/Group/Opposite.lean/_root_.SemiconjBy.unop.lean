import Mathlib

variable {α : Type*}

theorem _root_.SemiconjBy.unop [Mul α] {a x y : αᵐᵒᵖ} (h : SemiconjBy a x y) :
    SemiconjBy (unop a) (unop y) (unop x) := MulOpposite.semiconjBy_unop.2 h

