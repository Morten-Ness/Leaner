import Mathlib

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_symm_zero : (DirectSum.decompose ℳ).symm 0 = (0 : M) := map_zero (DirectSum.decomposeAddEquiv ℳ).symm

