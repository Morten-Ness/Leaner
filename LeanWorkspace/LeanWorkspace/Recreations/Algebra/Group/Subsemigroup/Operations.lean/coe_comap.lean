import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem coe_comap (S : Subsemigroup N) (f : M →ₙ* N) : (S.comap f : Set M) = f ⁻¹' S := rfl

