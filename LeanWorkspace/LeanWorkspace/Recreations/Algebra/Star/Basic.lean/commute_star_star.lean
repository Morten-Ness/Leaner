import Mathlib

open scoped Ring

variable {R : Type u}

variable [Mul R] [StarMul R]

theorem commute_star_star {x y : R} : Commute (star x) (star y) ↔ Commute x y := semiconjBy_star_star_star

alias ⟨_, Commute.star_star⟩ := commute_star_star

