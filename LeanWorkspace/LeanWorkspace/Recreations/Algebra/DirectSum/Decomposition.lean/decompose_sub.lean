import Mathlib

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommGroup M]

variable [SetLike σ M] [AddSubgroupClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_sub (x y : M) : DirectSum.decompose ℳ (x - y) = DirectSum.decompose ℳ x - DirectSum.decompose ℳ y := map_sub (DirectSum.decomposeAddEquiv ℳ) x y

