import Mathlib

variable {ι α R S : Type*}

variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)

theorem pos_iff {x : R} : 0 < abv x ↔ x ≠ 0 := (AbsoluteValue.nonneg abv x).lt_iff_ne'.trans AbsoluteValue.ne_zero_iff abv
protected alias ⟨_, pos⟩ := AbsoluteValue.pos_iff

