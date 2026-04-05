import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {σ : Type t} [CommRing R] [CommRing S] [Algebra R S]
  (pres : Algebra.Presentation R S ι σ)

set_option backward.isDefEq.respectTransparency false in
theorem comm₂₃' : pres.toExtension.toKaehler.comp pres.cotangentSpaceBasis.repr.symm.toLinearMap =
    Finsupp.linearCombination S (fun g ↦ D _ _ (pres.val g)) := by
  ext
  simp

