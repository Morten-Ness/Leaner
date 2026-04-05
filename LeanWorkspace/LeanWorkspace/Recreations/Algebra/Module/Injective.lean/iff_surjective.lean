import Mathlib

variable (R : Type u) [Ring R] (Q : Type v) [AddCommGroup Q] [Module R Q]

variable {R Q} {M N : Type*} [AddCommGroup M] [AddCommGroup N]

variable [Module R M] [Module R N] (i : M →ₗ[R] N) (f : M →ₗ[R] Q)

theorem iff_surjective {R : Type u} [CommRing R] [Module R M] : Module.Baer R M ↔
    ∀ (I : Ideal R), Function.Surjective (LinearMap.lcomp R M I.subtype) := by
  refine ⟨fun h I g ↦ ?_, fun h I g ↦ ?_⟩
  · rcases h I g with ⟨g', hg'⟩
    use g'
    ext x
    simp [hg']
  · rcases h I g with ⟨g', hg'⟩
    use g'
    intro x hx
    simp [← hg']

