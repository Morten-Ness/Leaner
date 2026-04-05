import Mathlib

variable {α : Type*}

theorem _root_.Commute.op [Mul α] {x y : α} (h : Commute x y) : Commute (op x) (op y) := SemiconjBy.op h

