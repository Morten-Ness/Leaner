import Mathlib

variable {R S M N : Type*}

variable [Semiring R] [Semiring S]

variable [AddCommMonoid M] [Module R M] [Module S M] [AddCommMonoid N] [Module R N]
  {r : R} {m m₁ m₂ : M}

variable [IsTorsionFree R M]

variable [IsCancelMulZero R]

variable [CharZero R]

include R in
theorem IsAddTorsionFree.of_isTorsionFree : IsAddTorsionFree M where
  nsmul_right_injective n hn := by
    simp_rw [← Nat.cast_smul_eq_nsmul R]; apply smul_right_injective; simpa

