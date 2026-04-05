import Mathlib

variable {S M G : Type*}

variable [MulOneClass M]

theorem one_left (x : M) : SemiconjBy 1 x x := Eq.symm <| SemiconjBy.one_right x

