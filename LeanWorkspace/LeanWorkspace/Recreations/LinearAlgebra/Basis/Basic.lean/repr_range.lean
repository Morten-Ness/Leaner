import Mathlib

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  (b : Basis ι R M)

theorem repr_range : LinearMap.range (b.repr : M →ₗ[R] ι →₀ R) = Finsupp.supported R R Set.univ := by
  rw [LinearEquiv.range, Finsupp.supported_univ]

