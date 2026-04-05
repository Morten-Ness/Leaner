import Mathlib

variable {R : Type*} [Semiring R] {P : Type*} [AddCommMonoid P] [Module R P] {M : Type*}
  [AddCommMonoid M] [Module R M] {N : Type*} [AddCommMonoid N] [Module R N]

variable {Q : Type*} [AddCommMonoid Q] [Module R Q]

variable {ι : Type*} (A : ι → Type*) [∀ i : ι, AddCommMonoid (A i)] [∀ i : ι, Module R (A i)]

theorem Projective.of_split [Module.Projective R M]
    (i : P →ₗ[R] M) (s : M →ₗ[R] P) (H : s.comp i = LinearMap.id) : Module.Projective R P := by
  obtain ⟨g, hg⟩ := Module.projective_lifting_property (Finsupp.linearCombination R id) s
    (fun x ↦ ⟨Finsupp.single x 1, by simp⟩)
  refine ⟨g.comp i, fun x ↦ ?_⟩
  rw [LinearMap.comp_apply, ← LinearMap.comp_apply, hg,
    ← LinearMap.comp_apply, H, LinearMap.id_apply]

