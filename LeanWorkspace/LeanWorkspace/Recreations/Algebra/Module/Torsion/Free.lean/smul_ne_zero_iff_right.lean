import Mathlib

variable {R S M N : Type*}

variable [Semiring R] [Semiring S]

variable [AddCommMonoid M] [Module R M] [Module S M] [AddCommMonoid N] [Module R N]
  {r : R} {m m₁ m₂ : M}

variable [IsTorsionFree R M]

variable [IsCancelMulZero R]

theorem smul_ne_zero_iff_right (hr : r ≠ 0) : r • m ≠ 0 ↔ m ≠ 0 := (smul_eq_zero_iff_right hr).ne

