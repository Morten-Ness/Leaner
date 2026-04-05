import Mathlib

variable {ι k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

theorem affineCombination_mem_affineSpan [Nontrivial k] {s : Finset ι} {w : ι → k}
    (h : ∑ i ∈ s, w i = 1) (p : ι → P) :
    s.affineCombination k p w ∈ affineSpan k (Set.range p) := by
  classical
    have hnz : ∑ i ∈ s, w i ≠ 0 := h.symm ▸ one_ne_zero
    have hn : s.Nonempty := Finset.nonempty_of_sum_ne_zero hnz
    obtain ⟨i1, hi1⟩ := hn
    let w1 : ι → k := Function.update (Function.const ι 0) i1 1
    have hw1 : ∑ i ∈ s, w1 i = 1 := by
      simp only [w1, Function.const_zero, Finset.sum_update_of_mem hi1, Pi.zero_apply,
          Finset.sum_const_zero, add_zero]
    have hw1s : s.affineCombination k p w1 = p i1 :=
      Finset.affineCombination_of_eq_one_of_eq_zero s w1 p hi1 (Function.update_self ..) fun _ _ hne =>
        Function.update_of_ne hne ..
    have hv : s.affineCombination k p w -ᵥ p i1 ∈ (affineSpan k (Set.range p)).direction := by
      rw [direction_affineSpan, ← hw1s, Finset.affineCombination_vsub]
      apply weightedVSub_mem_vectorSpan
      simp [Pi.sub_apply, h, hw1]
    rw [← vsub_vadd (s.affineCombination k p w) (p i1)]
    exact AffineSubspace.vadd_mem_of_mem_direction hv (mem_affineSpan k (Set.mem_range_self _))

