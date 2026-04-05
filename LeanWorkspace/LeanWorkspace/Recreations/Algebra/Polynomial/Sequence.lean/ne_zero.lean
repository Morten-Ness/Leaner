import Mathlib

open scoped Function

variable (R : Type*)

variable [Semiring R] (S : Sequence R)

theorem ne_zero (i : ℕ) : S i ≠ 0 := degree_ne_bot.mp <| by simp [S.degree_eq i]

