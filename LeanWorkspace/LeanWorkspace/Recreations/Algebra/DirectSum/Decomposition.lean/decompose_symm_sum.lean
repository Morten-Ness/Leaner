import Mathlib

open scoped DirectSum

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_symm_sum {ι'} (s : Finset ι') (f : ι' → ⨁ i, ℳ i) :
    (DirectSum.decompose ℳ).symm (∑ i ∈ s, f i) = ∑ i ∈ s, (DirectSum.decompose ℳ).symm (f i) := map_sum (DirectSum.decomposeAddEquiv ℳ).symm f s

