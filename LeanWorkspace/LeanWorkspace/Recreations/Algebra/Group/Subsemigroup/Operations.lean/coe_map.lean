import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem coe_map (f : M →ₙ* N) (S : Subsemigroup M) : (S.map f : Set N) = f '' S := rfl

