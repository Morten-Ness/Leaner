import Mathlib

open scoped DirectSum

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommGroup M]

variable [SetLike σ M] [AddSubgroupClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_symm_sub (x y : ⨁ i, ℳ i) :
    (DirectSum.decompose ℳ).symm (x - y) = (DirectSum.decompose ℳ).symm x - (DirectSum.decompose ℳ).symm y := map_sub (DirectSum.decomposeAddEquiv ℳ).symm x y

