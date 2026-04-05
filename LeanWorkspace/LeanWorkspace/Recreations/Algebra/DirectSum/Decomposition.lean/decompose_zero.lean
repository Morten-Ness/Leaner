import Mathlib

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_zero : DirectSum.decompose ℳ (0 : M) = 0 := map_zero (DirectSum.decomposeAddEquiv ℳ)

