import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

theorem prev_nat_zero : CochainComplex.prev (ComplexShape.up ℕ) 0 = 0 := by
  classical
    refine dif_neg ?_
    push Not
    intro
    apply Nat.noConfusion

