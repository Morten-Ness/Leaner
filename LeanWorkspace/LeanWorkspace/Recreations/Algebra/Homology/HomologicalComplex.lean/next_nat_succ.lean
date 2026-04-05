import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

theorem next_nat_succ (i : ℕ) : ChainComplex.next (ComplexShape.down ℕ) (i + 1) = i := (ComplexShape.down ℕ).next_eq' rfl

