import Mathlib

variable {ι k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable (k) in

variable (k V)

theorem mem_affineSpan_iff_eq_affineCombination [Nontrivial k] {p1 : P} {p : ι → P} :
    p1 ∈ affineSpan k (Set.range p) ↔
      ∃ (s : Finset ι) (w : ι → k), ∑ i ∈ s, w i = 1 ∧ p1 = s.affineCombination k p w := by
  constructor
  · exact eq_affineCombination_of_mem_affineSpan
  · rintro ⟨s, w, hw, rfl⟩
    exact affineCombination_mem_affineSpan hw p

