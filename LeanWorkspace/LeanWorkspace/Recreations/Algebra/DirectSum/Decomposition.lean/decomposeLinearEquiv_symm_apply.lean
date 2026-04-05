import Mathlib

open scoped DirectSum

variable {ι R M σ : Type*}

variable [DecidableEq ι] [Semiring R] [AddCommMonoid M] [Module R M]

variable (ℳ : ι → Submodule R M)

variable [Decomposition ℳ]

theorem decomposeLinearEquiv_symm_apply (m : ⨁ i, ℳ i) :
    (DirectSum.decomposeLinearEquiv ℳ).symm m = (DirectSum.decompose ℳ).symm m := rfl

