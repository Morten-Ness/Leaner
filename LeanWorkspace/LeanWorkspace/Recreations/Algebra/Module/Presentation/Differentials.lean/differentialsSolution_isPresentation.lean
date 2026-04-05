import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {σ : Type t} [CommRing R] [CommRing S] [Algebra R S]
  (pres : Algebra.Presentation R S ι σ)

theorem differentialsSolution_isPresentation :
    pres.differentialsSolution.IsPresentation := by
  rw [Module.Relations.Solution.isPresentation_iff]
  constructor
  · rw [← Module.Relations.Solution.surjective_π_iff_span_eq_top, ← comm₂₃]
    exact Extension.toKaehler_surjective.comp pres.cotangentSpaceBasis.repr.symm.surjective
  · rw [← Module.Relations.range_map]
    exact Function.Exact.linearMap_ker_eq
      ((LinearMap.exact_iff_of_surjective_of_bijective_of_injective
      _ _ _ _ (Algebra.Presentation.differentials.hom₁ pres)
      pres.cotangentSpaceBasis.repr.symm.toLinearMap .id
      (Algebra.Presentation.differentials.comm₁₂ pres) (by simpa using comm₂₃ pres) (Algebra.Presentation.differentials.surjective_hom₁ pres)
        (LinearEquiv.bijective _) (Equiv.refl _).injective).2
        pres.toExtension.exact_cotangentComplex_toKaehler)

