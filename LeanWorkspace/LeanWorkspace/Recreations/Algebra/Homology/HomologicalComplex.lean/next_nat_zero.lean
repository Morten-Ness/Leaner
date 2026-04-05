import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

theorem next_nat_zero : ChainComplex.next (ComplexShape.down ℕ) 0 = 0 := by
  classical
    refine dif_neg ?_
    push Not
    intro
    apply Nat.noConfusion

