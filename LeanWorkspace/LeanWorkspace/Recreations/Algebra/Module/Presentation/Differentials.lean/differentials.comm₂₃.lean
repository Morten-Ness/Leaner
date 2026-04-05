import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {σ : Type t} [CommRing R] [CommRing S] [Algebra R S]
  (pres : Algebra.Presentation R S ι σ)

theorem differentials.comm₂₃ :
    pres.toExtension.toKaehler.comp pres.cotangentSpaceBasis.repr.symm.toLinearMap =
      pres.differentialsSolution.π := Algebra.Presentation.differentials.comm₂₃' pres

