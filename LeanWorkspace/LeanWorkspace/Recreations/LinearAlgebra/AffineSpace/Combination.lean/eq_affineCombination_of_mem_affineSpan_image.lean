import Mathlib

variable {ι k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable (k) in

theorem eq_affineCombination_of_mem_affineSpan_image {p₁ : P} {p : ι → P} {s : Set ι}
    (h : p₁ ∈ affineSpan k (p '' s)) :
    ∃ (fs : Finset ι) (w : ι → k), ↑fs ⊆ s ∧ ∑ i ∈ fs, w i = 1 ∧
      p₁ = fs.affineCombination k p w := by
  classical
  rw [Set.image_eq_range] at h
  obtain ⟨fs', w', hw', rfl⟩ := eq_affineCombination_of_mem_affineSpan h
  refine ⟨fs'.map (Function.Embedding.subtype _), fun i ↦ if hi : i ∈ s then w' ⟨i, hi⟩ else 0,
    (by simp), (by simp [hw']), ?_⟩
  simp only [Finset.affineCombination_map, Function.Embedding.coe_subtype]
  exact Finset.affineCombination_congr fs' (by simp) (by simp)

