import Mathlib

variable {α : Type*}

theorem untop₀_mul [DecidableEq α] [MulZeroClass α] (a b : WithTop α) :
    (a * b).untop₀ = a.untop₀ * b.untop₀ := untopD_zero_mul a b

