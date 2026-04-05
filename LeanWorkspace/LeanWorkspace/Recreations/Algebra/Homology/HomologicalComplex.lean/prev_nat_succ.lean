import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

theorem prev_nat_succ (i : ℕ) : CochainComplex.prev (ComplexShape.up ℕ) (i + 1) = i := (ComplexShape.up ℕ).prev_eq' rfl

