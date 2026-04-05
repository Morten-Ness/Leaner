import Mathlib

variable {R : Type*} [Semiring R] {P : Type*} [AddCommMonoid P] [Module R P] {M : Type*}
  [AddCommMonoid M] [Module R M] {N : Type*} [AddCommMonoid N] [Module R N]

variable {Q : Type*} [AddCommMonoid Q] [Module R Q]

variable {ι : Type*} (A : ι → Type*) [∀ i : ι, AddCommMonoid (A i)] [∀ i : ι, Module R (A i)]

theorem Projective.of_equiv' [Module.Projective R M]
    (e : M ≃ₗ[R] P) : Module.Projective R P := .of_equiv e

