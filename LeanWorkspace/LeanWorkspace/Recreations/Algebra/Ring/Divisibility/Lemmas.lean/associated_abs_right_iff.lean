import Mathlib

variable {R : Type*}

variable [Ring R] [LinearOrder R] {x y : R}

theorem associated_abs_right_iff :
    Associated x |y| ↔ Associated x y := by
  rw [Associated.comm, associated_abs_left_iff, Associated.comm]

alias ⟨_, Associated.abs_left⟩ := associated_abs_left_iff

alias ⟨_, Associated.abs_right⟩ := associated_abs_right_iff

