import Mathlib

variable {k V V₂ P P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

theorem affineCombination_mem_setInterior_iff {I : Set k} {n : ℕ} {s : Affine.Simplex k P n}
    {w : Fin (n + 1) → k} (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination k s.points w ∈ s.setInterior I ↔ ∀ i, w i ∈ I := by
  refine ⟨fun ⟨w', hw', hw'01, hww'⟩ ↦ ?_, fun h ↦ ⟨w, hw, h, rfl⟩⟩
  simp_rw [← (affineIndependent_iff_eq_of_fintype_affineCombination_eq k s.points).1
    s.independent w' w hw' hw hww']
  exact hw'01

