import Mathlib

open scoped DirectSum

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_symm_add (x y : ⨁ i, ℳ i) :
    (DirectSum.decompose ℳ).symm (x + y) = (DirectSum.decompose ℳ).symm x + (DirectSum.decompose ℳ).symm y := map_add (DirectSum.decomposeAddEquiv ℳ).symm x y

