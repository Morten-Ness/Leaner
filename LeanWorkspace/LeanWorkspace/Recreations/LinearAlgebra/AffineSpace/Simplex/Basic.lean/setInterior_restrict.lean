import Mathlib

variable {k V V₂ P P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

theorem setInterior_restrict (I : Set k) {n : ℕ} (s : Affine.Simplex k P n) {S : AffineSubspace k P}
    (hS : affineSpan k (Set.range s.points) ≤ S) :
    letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
    (s.restrict S hS).setInterior I = S.subtype ⁻¹' (s.setInterior I) := by
  letI := Nonempty.map (AffineSubspace.inclusion hS) inferInstance
  rw [← S.subtype_injective.image_injective.eq_iff,
    Set.image_preimage_eq_of_subset (s.setInterior_subset_affineSpan.trans (by simpa using hS)),
    ← (s.restrict S hS).setInterior_map I S.subtype_injective]
  rfl

