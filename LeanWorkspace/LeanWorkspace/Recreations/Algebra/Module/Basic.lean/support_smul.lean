import Mathlib

variable {α R M M₂ : Type*}

theorem support_smul [Semiring R] [IsDomain R] [AddCommMonoid M] [Module R M]
    [Module.IsTorsionFree R M] (f : α → R) (g : α → M) : support (f • g) = support f ∩ support g := ext fun _ => smul_ne_zero_iff

