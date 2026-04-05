import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

theorem next (α : Type*) [AddGroup α] [One α] (i : α) : (ComplexShape.down α).next i = i - 1 := (ComplexShape.down α).next_eq' <| sub_add_cancel _ _

