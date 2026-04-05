import Mathlib

variable (R : Type u) (M : Type*) [Ring R] [AddCommGroup M] [Module R M]

theorem Module.FinitePresentation.exists_fin [fp : Module.FinitePresentation R M] :
    ∃ (n : ℕ) (K : Submodule R (Fin n → R)) (_ : M ≃ₗ[R] (Fin n → R) ⧸ K), K.FG := by
  have ⟨ι, ⟨hι₁, hι₂⟩⟩ := fp
  refine ⟨_, LinearMap.ker (linearCombination R Subtype.val ∘ₗ
    (lcongr ι.equivFin (.refl ..) ≪≫ₗ linearEquivFunOnFinite R R _).symm.toLinearMap),
    (LinearMap.quotKerEquivOfSurjective _ <| LinearMap.range_eq_top.mp ?_).symm, ?_⟩
  · simpa [range_linearCombination] using hι₁
  · simpa [LinearMap.ker_comp, Submodule.comap_equiv_eq_map_symm] using hι₂.map _

