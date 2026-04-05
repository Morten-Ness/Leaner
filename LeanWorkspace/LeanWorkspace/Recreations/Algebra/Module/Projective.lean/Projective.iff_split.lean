import Mathlib

variable {R : Type u} [Semiring R] {P : Type v} [AddCommMonoid P] [Module R P]

variable {R₀ M N} [CommSemiring R₀] [Algebra R₀ R] [AddCommMonoid M] [Module R₀ M] [Module R M]

variable [IsScalarTower R₀ R M] [AddCommMonoid N] [Module R₀ N]

theorem Projective.iff_split : Module.Projective R P ↔
    ∃ (M : Type max u v) (_ : AddCommMonoid M) (_ : Module R M) (_ : Module.Free R M)
      (i : P →ₗ[R] M) (s : M →ₗ[R] P), s.comp i = LinearMap.id := Module.Projective.iff_split'.{max u v}

