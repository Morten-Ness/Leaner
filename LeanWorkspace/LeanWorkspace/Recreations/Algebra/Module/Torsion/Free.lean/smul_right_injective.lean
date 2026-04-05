import Mathlib

variable {R S M N : Type*}

variable [Semiring R] [Semiring S]

variable [AddCommMonoid M] [Module R M] [Module S M] [AddCommMonoid N] [Module R N]
  {r : R} {m m₁ m₂ : M}

variable [IsTorsionFree R M]

variable [IsCancelMulZero R]

theorem smul_right_injective (hr : r ≠ 0) : ((r • ·) : M → M).Injective := (IsRegular.of_ne_zero hr).smul_right_injective _

