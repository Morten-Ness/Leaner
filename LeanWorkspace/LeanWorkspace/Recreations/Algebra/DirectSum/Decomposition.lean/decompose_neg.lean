import Mathlib

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommGroup M]

variable [SetLike σ M] [AddSubgroupClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_neg (x : M) : DirectSum.decompose ℳ (-x) = -DirectSum.decompose ℳ x := map_neg (DirectSum.decomposeAddEquiv ℳ) x

