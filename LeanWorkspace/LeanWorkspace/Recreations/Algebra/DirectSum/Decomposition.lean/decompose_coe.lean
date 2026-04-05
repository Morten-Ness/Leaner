import Mathlib

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem decompose_coe {i : ι} (x : ℳ i) : DirectSum.decompose ℳ (x : M) = DirectSum.of _ i x := by
  rw [← DirectSum.decompose_symm_of _, Equiv.apply_symm_apply]

