import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {σ : Type t} [CommRing R] [CommRing S] [Algebra R S]
  (pres : Algebra.Presentation R S ι σ)

set_option backward.isDefEq.respectTransparency false in
theorem hom₁_single (r : σ) :
    Algebra.Presentation.differentials.hom₁ pres (Finsupp.single r 1) = Extension.Cotangent.mk ⟨pres.relation r, by simp⟩ := by
  simp [Algebra.Presentation.differentials.hom₁]

