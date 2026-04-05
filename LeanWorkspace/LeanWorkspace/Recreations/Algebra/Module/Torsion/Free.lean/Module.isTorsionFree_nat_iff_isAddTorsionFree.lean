import Mathlib

variable {R S M N : Type*}

variable [Semiring R] [Semiring S]

variable [AddCommMonoid M] [Module R M] [Module S M] [AddCommMonoid N] [Module R N]
  {r : R} {m m₁ m₂ : M}

variable [IsTorsionFree R M]

variable [IsCancelMulZero R]

variable [CharZero R]

theorem Module.isTorsionFree_nat_iff_isAddTorsionFree : IsTorsionFree ℕ M ↔ IsAddTorsionFree M where
  mp _ := .of_isTorsionFree ℕ _
  mpr _ := inferInstance

