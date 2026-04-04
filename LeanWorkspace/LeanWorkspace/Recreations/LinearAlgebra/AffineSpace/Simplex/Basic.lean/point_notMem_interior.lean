import Mathlib

variable {k V V₂ P P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [PartialOrder k]

theorem point_notMem_interior {n : ℕ} (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.points i ∉ s.interior := by
  rw [← Finset.univ.affineCombination_affineCombinationSingleWeights k s.points
    (Finset.mem_univ i), Affine.Simplex.affineCombination_mem_interior_iff
      (sum_affineCombinationSingleWeights _ _ (Finset.mem_univ i)), not_forall]
  exact ⟨i, by simp⟩

