import Mathlib

variable {α R M M₂ : Type*}

theorem support_const_smul_of_ne_zero [Semiring R] [IsDomain R] [AddCommMonoid M] [Module R M]
    [Module.IsTorsionFree R M] (c : R) (g : α → M) (hc : c ≠ 0) : support (c • g) = support g := ext fun _ ↦ smul_ne_zero_iff_right hc

