import Mathlib

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_sum {ι'} (s : Finset ι') (f : ι' → M) :
    DirectSum.decompose ℳ (∑ i ∈ s, f i) = ∑ i ∈ s, DirectSum.decompose ℳ (f i) := map_sum (DirectSum.decomposeAddEquiv ℳ) f s

