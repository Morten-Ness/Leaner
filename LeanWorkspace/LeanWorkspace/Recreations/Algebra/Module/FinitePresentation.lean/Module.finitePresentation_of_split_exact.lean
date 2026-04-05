import Mathlib

variable (R M N) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

variable {ι} [Finite ι]

theorem Module.finitePresentation_of_split_exact
    {P : Type*} [AddCommGroup P] [Module R P]
    [Module.FinitePresentation R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (l : P →ₗ[R] N) (hl : g ∘ₗ l = .id)
    (hf : Function.Injective f) (H : Function.Exact f g) :
    Module.FinitePresentation R M := by
  have hg : Function.Surjective g := Function.LeftInverse.surjective (DFunLike.congr_fun hl)
  have := Module.Finite.of_surjective g hg
  obtain ⟨e, rfl, rfl⟩ := ((Function.Exact.split_tfae' H).out 0 2 rfl rfl).mp
    ⟨hf, l, hl⟩
  refine Module.finitePresentation_of_surjective (LinearMap.fst _ _ _ ∘ₗ e.toLinearMap)
    (Prod.fst_surjective.comp e.surjective) ?_
  rw [LinearMap.ker_comp, Submodule.comap_equiv_eq_map_symm,
    LinearMap.exact_iff.mp Function.Exact.inr_fst, ← LinearMap.range_comp]
  exact Submodule.fg_range _

