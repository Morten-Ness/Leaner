import Mathlib

variable {ι α R S : Type*}

variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)

theorem ne_zero_iff {x : R} : abv x ≠ 0 ↔ x ≠ 0 := AbsoluteValue.eq_zero abv.not
protected alias ⟨_, ne_zero⟩ := AbsoluteValue.ne_zero_iff

