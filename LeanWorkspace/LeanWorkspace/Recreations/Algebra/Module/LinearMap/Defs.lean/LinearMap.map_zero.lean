import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable [Semiring R] [Semiring S]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂] [Module S M₃]

variable (σ : R →+* S)

variable (fₗ : M →ₗ[R] M₂) (f g : M →ₛₗ[σ] M₃)

theorem map_zero : f 0 = 0 := map_zero f

-- Porting note: `simp` wasn't picking up `map_smulₛₗ` for `LinearMap`s without specifying
-- `map_smulₛₗ f`, so we marked this as `@[simp]` in Mathlib3.
-- For Mathlib4, let's try without the `@[simp]` attribute and hope it won't need to be re-enabled.
-- This has to be re-tagged as `@[simp]` in https://github.com/leanprover-community/mathlib4/pull/8386 (see also https://github.com/leanprover/lean4/issues/3107).

