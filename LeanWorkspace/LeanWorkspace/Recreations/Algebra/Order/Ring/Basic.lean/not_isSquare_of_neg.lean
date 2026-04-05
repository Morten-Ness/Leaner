import Mathlib

variable {α M R : Type*}

theorem not_isSquare_of_neg [Semiring R] [LinearOrder R]
    [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R]
    {x : R} (h : x < 0) : ¬ IsSquare x := (h.not_ge ·.nonneg)

