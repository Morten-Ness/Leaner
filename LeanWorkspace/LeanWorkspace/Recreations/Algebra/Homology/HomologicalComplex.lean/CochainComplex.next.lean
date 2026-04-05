import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

theorem next (α : Type*) [AddRightCancelSemigroup α] [One α] (i : α) :
    ChainComplex.next (ComplexShape.up α) i = i + 1 := (ComplexShape.up α).next_eq' rfl

