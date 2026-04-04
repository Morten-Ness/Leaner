import Mathlib

variable {k V V₂ P P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [PartialOrder k]

theorem closedInterior_restrict {n : ℕ} (s : Affine.Simplex k P n) {S : AffineSubspace k P}
    (hS : affineSpan k (Set.range s.points) ≤ S) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).closedInterior = S.subtype ⁻¹' s.closedInterior :=
  s.setInterior_restrict _ hS

