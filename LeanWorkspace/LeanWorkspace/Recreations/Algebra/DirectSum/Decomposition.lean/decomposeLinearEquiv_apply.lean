import Mathlib

variable {ι R M σ : Type*}

variable [DecidableEq ι] [Semiring R] [AddCommMonoid M] [Module R M]

variable (ℳ : ι → Submodule R M)

variable [Decomposition ℳ]

theorem decomposeLinearEquiv_apply (m : M) :
    DirectSum.decomposeLinearEquiv ℳ m = DirectSum.decompose ℳ m := rfl

