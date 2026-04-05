import Mathlib

variable {R : Type*}

theorem IsSquare.isSumSq [AddZeroClass R] [Mul R] {x : R} (hx : IsSquare x) : IsSumSq x := by aesop

attribute [simp, aesop safe] IsSumSq.zero

