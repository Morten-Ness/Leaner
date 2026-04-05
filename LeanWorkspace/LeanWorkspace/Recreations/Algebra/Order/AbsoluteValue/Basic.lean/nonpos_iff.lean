import Mathlib

variable {ι α R S : Type*}

variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)

theorem nonpos_iff {x : R} : abv x ≤ 0 ↔ x = 0 := by
  simp only [← AbsoluteValue.eq_zero abv, le_antisymm_iff, AbsoluteValue.nonneg abv, and_true]

