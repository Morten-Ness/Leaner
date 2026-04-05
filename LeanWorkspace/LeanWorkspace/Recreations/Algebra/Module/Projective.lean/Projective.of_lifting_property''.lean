import Mathlib

variable {R : Type*} [Semiring R] {P : Type*} [AddCommMonoid P] [Module R P] {M : Type*}
  [AddCommMonoid M] [Module R M] {N : Type*} [AddCommMonoid N] [Module R N]

theorem Projective.of_lifting_property'' {R : Type u} [Semiring R] {P : Type v} [AddCommMonoid P]
    [Module R P] (huniv : ∀ (f : (P →₀ R) →ₗ[R] P), Function.Surjective f →
      ∃ h : P →ₗ[R] (P →₀ R), f.comp h = .id) :
    Projective R P := Module.projective_def'.2 <| huniv (Finsupp.linearCombination R (id : P → P))
    (linearCombination_surjective _ Function.surjective_id)

