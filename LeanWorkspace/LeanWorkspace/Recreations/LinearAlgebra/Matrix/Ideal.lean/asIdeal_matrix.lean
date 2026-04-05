import Mathlib

variable {R : Type*} (n : Type*)

variable [Ring R] [Fintype n]

theorem asIdeal_matrix [DecidableEq n] (I : TwoSidedIdeal R) :
    asIdeal (I.matrix n) = (asIdeal I).matrix n := by
  ext; simp

