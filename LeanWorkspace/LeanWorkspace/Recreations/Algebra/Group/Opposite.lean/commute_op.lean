import Mathlib

variable {α : Type*}

theorem commute_op [Mul α] {x y : α} : Commute (op x) (op y) ↔ Commute x y := MulOpposite.semiconjBy_op

