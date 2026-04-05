import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {σ : Type t} [CommRing R] [CommRing S] [Algebra R S]
  (pres : Algebra.Presentation R S ι σ)

set_option backward.isDefEq.respectTransparency false in
theorem comm₁₂ : pres.toExtension.cotangentComplex.comp (Algebra.Presentation.differentials.hom₁ pres) =
    pres.cotangentSpaceBasis.repr.symm.comp (Algebra.Presentation.differentialsRelations pres).map := by
  ext r
  have := (Algebra.Presentation.differentialsRelations pres).map_single
  dsimp at this ⊢
  rw [Algebra.Presentation.differentials.comm₁₂_single, this]

