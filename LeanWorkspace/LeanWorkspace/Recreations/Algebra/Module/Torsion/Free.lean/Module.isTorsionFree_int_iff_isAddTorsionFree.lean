import Mathlib

variable {R S M N : Type*}

variable [Semiring R] [Semiring S]

variable [CharZero R] [IsDomain R] [AddCommGroup M] [Module R M] {m : M}

theorem Module.isTorsionFree_int_iff_isAddTorsionFree : IsTorsionFree ℤ M ↔ IsAddTorsionFree M where
  mp _ := .of_isTorsionFree ℤ _
  mpr _ := inferInstance

