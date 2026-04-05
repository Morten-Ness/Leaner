import Mathlib

variable {k V V₂ P P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

theorem setInterior_map (I : Set k) {n : ℕ} (s : Affine.Simplex k P n) {f : P →ᵃ[k] P₂}
    (hf : Function.Injective f) : (s.map f hf).setInterior I = f '' s.setInterior I := by
  ext p
  rw [Set.mem_image]
  by_cases hp : p ∈ affineSpan k (Set.range (s.map f hf).points)
  · obtain ⟨w, hw1, hw⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
    rw [hw, Affine.Simplex.affineCombination_mem_setInterior_iff hw1, Affine.Simplex.map_points,
      ← Finset.map_affineCombination _ _ _ hw1]
    simp_rw [hf.eq_iff]
    simp [Affine.Simplex.affineCombination_mem_setInterior_iff hw1]
  · apply iff_of_false
    · exact fun h ↦ hp (Set.mem_of_mem_of_subset h (s.map f hf).setInterior_subset_affineSpan)
    · contrapose! hp
      obtain ⟨q, hq, hqp⟩ := hp
      rw [s.map_points, Set.range_comp, ← AffineSubspace.map_span, AffineSubspace.mem_map]
      exact ⟨q, (Set.mem_of_mem_of_subset hq Affine.Simplex.setInterior_subset_affineSpan s), hqp⟩

