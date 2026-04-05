import Mathlib

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_symm_of {i : ι} (x : ℳ i) : (DirectSum.decompose ℳ).symm (DirectSum.of _ i x) = x := DirectSum.coeAddMonoidHom_of ℳ _ _

