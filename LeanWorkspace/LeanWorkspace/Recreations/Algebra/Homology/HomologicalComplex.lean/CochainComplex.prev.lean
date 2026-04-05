import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

theorem prev (α : Type*) [AddGroup α] [One α] (i : α) : ChainComplex.prev (ComplexShape.up α) i = i - 1 := (ComplexShape.up α).prev_eq' <| sub_add_cancel _ _

