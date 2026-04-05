import Mathlib

variable {R M N N'} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

variable [AddCommGroup N'] [Module R N'] (S : Submonoid R) (f : N →ₗ[R] N') [IsLocalizedModule S f]

theorem Module.FinitePresentation.trans (S : Type*) [CommRing S] [Algebra R S]
    [Module S M] [IsScalarTower R S M] [Module.FinitePresentation R S]
    [Module.FinitePresentation S M] : Module.FinitePresentation R M := by
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin S M
  let f : (Fin n → S) →ₗ[R] M := (e.symm ∘ₗ K.mkQ).restrictScalars R
  refine Module.finitePresentation_of_surjective f (fun m ↦ ?_) ?_
  · obtain ⟨a, ha⟩ := K.mkQ_surjective (e m)
    exact ⟨a, by simp [f, ha]⟩
  · have : Module.Finite S
        (Submodule.restrictScalars R (LinearMap.ker (e.symm.toLinearMap ∘ₗ K.mkQ))) :=
      .of_fg <| show (LinearMap.ker (e.symm.toLinearMap ∘ₗ K.mkQ)).FG by simpa
    simp only [f, LinearMap.ker_restrictScalars, ← Module.Finite.iff_fg]
    exact Module.Finite.trans S _

