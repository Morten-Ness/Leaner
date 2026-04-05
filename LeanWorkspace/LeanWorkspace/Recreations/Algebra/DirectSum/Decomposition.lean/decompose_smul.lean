import Mathlib

variable {ι R M σ : Type*}

variable [DecidableEq ι] [Semiring R] [AddCommMonoid M] [Module R M]

variable (ℳ : ι → Submodule R M)

variable [Decomposition ℳ]

theorem decompose_smul (r : R) (x : M) : DirectSum.decompose ℳ (r • x) = r • DirectSum.decompose ℳ x := map_smul (DirectSum.decomposeLinearEquiv ℳ) r x

