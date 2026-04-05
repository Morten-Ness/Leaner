import Mathlib

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_add (x y : M) : DirectSum.decompose ℳ (x + y) = DirectSum.decompose ℳ x + DirectSum.decompose ℳ y := map_add (DirectSum.decomposeAddEquiv ℳ) x y

