import Mathlib

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem Decomposition.isInternal : DirectSum.IsInternal ℳ := ⟨Decomposition.right_inv.injective, Decomposition.left_inv.surjective⟩

