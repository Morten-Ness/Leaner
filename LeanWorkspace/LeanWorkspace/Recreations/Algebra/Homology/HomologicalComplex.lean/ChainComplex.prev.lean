import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

theorem prev (α : Type*) [AddRightCancelSemigroup α] [One α] (i : α) :
    (ComplexShape.down α).prev i = i + 1 := (ComplexShape.down α).prev_eq' rfl

