import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {σ : Type t} [CommRing R] [CommRing S] [Algebra R S]
  (pres : Algebra.Presentation R S ι σ)

set_option backward.isDefEq.respectTransparency false in
theorem comm₁₂_single (r : σ) :
    pres.toExtension.cotangentComplex (Algebra.Presentation.differentials.hom₁ pres (Finsupp.single r 1)) =
      pres.cotangentSpaceBasis.repr.symm ((Algebra.Presentation.differentialsRelations pres).relation r) := by
  simp only [Algebra.Presentation.differentials.hom₁, Finsupp.linearCombination_single, one_smul, Algebra.Presentation.differentialsRelations,
    Module.Basis.repr_symm_apply, Extension.cotangentComplex_mk]
  exact pres.cotangentSpaceBasis.repr.injective (by ext; simp)

