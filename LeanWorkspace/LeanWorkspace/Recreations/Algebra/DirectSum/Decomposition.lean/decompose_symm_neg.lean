import Mathlib

open scoped DirectSum

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommGroup M]

variable [SetLike σ M] [AddSubgroupClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_symm_neg (x : ⨁ i, ℳ i) : (DirectSum.decompose ℳ).symm (-x) = -(DirectSum.decompose ℳ).symm x := map_neg (DirectSum.decomposeAddEquiv ℳ).symm x

