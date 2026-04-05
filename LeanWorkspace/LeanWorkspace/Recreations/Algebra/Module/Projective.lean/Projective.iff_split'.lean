import Mathlib

variable {R : Type u} [Semiring R] {P : Type v} [AddCommMonoid P] [Module R P]

variable {R₀ M N} [CommSemiring R₀] [Algebra R₀ R] [AddCommMonoid M] [Module R₀ M] [Module R M]

variable [IsScalarTower R₀ R M] [AddCommMonoid N] [Module R₀ N]

theorem Projective.iff_split' [Small.{w} R] [Small.{w} P] : Module.Projective R P ↔
    ∃ (M : Type w) (_ : AddCommMonoid M) (_ : Module R M) (_ : Module.Free R M)
      (i : P →ₗ[R] M) (s : M →ₗ[R] P), s.comp i = LinearMap.id := by
  let e : (Shrink.{w, v} P →₀ Shrink.{w, u} R) ≃ₗ[R] P →₀ R :=
    Finsupp.mapDomain.linearEquiv _ R (equivShrink P).symm ≪≫ₗ
      Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R)
  refine ⟨fun ⟨i, hi⟩ ↦ ⟨(Shrink.{w} P) →₀ (Shrink.{w} R), _, _, Free.of_basis ⟨e⟩,
    e.symm.toLinearMap ∘ₗ i, (linearCombination R id) ∘ₗ e.toLinearMap, ?_⟩,
      fun ⟨_, _, _, _, i, s, H⟩ ↦ Module.Projective.of_split i s H⟩
  apply LinearMap.ext
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e.apply_symm_apply]
  exact hi

