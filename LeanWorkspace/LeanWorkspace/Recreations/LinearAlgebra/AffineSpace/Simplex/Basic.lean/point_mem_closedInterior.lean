import Mathlib

variable {k V V₂ P P₂ : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [PartialOrder k]

theorem point_mem_closedInterior [ZeroLEOneClass k] {n : ℕ} (s : Affine.Simplex k P n) (i : Fin (n + 1)) :
    s.points i ∈ s.closedInterior := by
  rw [← Finset.univ.affineCombination_affineCombinationSingleWeights k s.points
    (Finset.mem_univ i), Affine.Simplex.affineCombination_mem_closedInterior_iff
      (sum_affineCombinationSingleWeights _ _ (Finset.mem_univ i))]
  intro j
  by_cases hj : j = i <;> simp [hj]

