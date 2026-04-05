import Mathlib

variable {R : Type*}

variable [Ring R] [LinearOrder R] {x y : R}

theorem associated_abs_left_iff :
    Associated |x| y ↔ Associated x y := by
  obtain h | h := abs_choice x <;>
  simp [h]

