import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem coe_srange (f : M →ₙ* N) : (f.srange : Set N) = Set.range f := rfl

