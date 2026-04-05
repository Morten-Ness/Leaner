import Mathlib

theorem RingHom.surjective_of_epi_of_finite {R S : CommRingCat} (f : R ⟶ S) [Epi f]
    (h₂ : RingHom.Finite f.hom) : Function.Surjective f := by
  algebraize [f.hom]
  have : Algebra.IsEpi R S := CommRingCat.epi_iff_epi.mp <| inferInstanceAs (Epi f)
  rwa [Algebra.isEpi_iff_surjective_algebraMap_of_finite] at this

