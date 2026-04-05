import Mathlib

open scoped Ring

variable {R : Type u}

variable [Mul R] [StarMul R]

theorem commute_star_comm {x y : R} : Commute (star x) y ↔ Commute x (star y) := by
  rw [← commute_star_star, star_star]

alias ⟨Commute.star_right, Commute.star_left⟩ := commute_star_comm

