import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup V]

variable [Module k V] [AddTorsor V P] {ι : Type*}

theorem sign_eq_of_affineCombination_mem_affineSpan_single_lineMap {p : ι → P}
    (h : AffineIndependent k p) {w : ι → k} {s : Finset ι} (hw : ∑ i ∈ s, w i = 1) {i₁ i₂ i₃ : ι}
    (h₁ : i₁ ∈ s) (h₂ : i₂ ∈ s) (h₃ : i₃ ∈ s) (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    {c : k} (hc0 : 0 < c) (hc1 : c < 1)
    (hs : s.affineCombination k p w ∈ line[k, p i₁, AffineMap.lineMap (p i₂) (p i₃) c]) :
    SignType.sign (w i₂) = SignType.sign (w i₃) := by
  classical
    rw [← s.affineCombination_affineCombinationSingleWeights k p h₁, ←
      s.affineCombination_affineCombinationLineMapWeights p h₂ h₃ c] at hs
    refine
      sign_eq_of_affineCombination_mem_affineSpan_pair h hw
        (s.sum_affineCombinationSingleWeights k h₁)
        (s.sum_affineCombinationLineMapWeights h₂ h₃ c) hs h₂ h₃
        (Finset.affineCombinationSingleWeights_apply_of_ne k h₁₂.symm)
        (Finset.affineCombinationSingleWeights_apply_of_ne k h₁₃.symm) ?_
    rw [Finset.affineCombinationLineMapWeights_apply_left h₂₃,
      Finset.affineCombinationLineMapWeights_apply_right h₂₃]
    simp_all only [sub_pos, sign_pos]

