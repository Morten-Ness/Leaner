import Mathlib

variable {R : Type*} [Semiring R] {P : Type*} [AddCommMonoid P] [Module R P] {M : Type*}
  [AddCommMonoid M] [Module R M] {N : Type*} [AddCommMonoid N] [Module R N]

variable {Q : Type*} [AddCommMonoid Q] [Module R Q]

variable {ι : Type*} (A : ι → Type*) [∀ i : ι, AddCommMonoid (A i)] [∀ i : ι, Module R (A i)]

theorem Projective.iff_split_of_projective [Module.Projective R M] (s : M →ₗ[R] P)
    (hs : Function.Surjective s) :
    Module.Projective R P ↔ ∃ i, s ∘ₗ i = LinearMap.id := ⟨fun _ ↦ Module.projective_lifting_property _ _ hs, fun ⟨i, H⟩ ↦ Module.Projective.of_split i s H⟩

