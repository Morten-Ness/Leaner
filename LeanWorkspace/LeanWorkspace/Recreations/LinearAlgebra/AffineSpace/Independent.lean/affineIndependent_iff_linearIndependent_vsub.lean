import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

theorem affineIndependent_iff_linearIndependent_vsub (p : ι → P) (i1 : ι) :
    AffineIndependent k p ↔ LinearIndependent k fun i : { x // x ≠ i1 } => (p i -ᵥ p i1 : V) := by
  classical
    constructor
    · intro h
      rw [linearIndependent_iff']
      intro s g hg i hi
      set f : ι → k := fun x => if hx : x = i1 then -∑ y ∈ s, g y else g ⟨x, hx⟩ with hfdef
      let s2 : Finset ι := insert i1 (s.map (Embedding.subtype _))
      have hfg : ∀ x : { x // x ≠ i1 }, g x = f x := by grind
      rw [hfg]
      have hf : ∑ ι ∈ s2, f ι = 0 := by
        rw [Finset.sum_insert
            (Finset.notMem_map_subtype_of_not_property s (Classical.not_not.2 rfl)),
          Finset.sum_subtype_map_embedding fun x _ => (hfg x).symm]
        rw [hfdef]
        dsimp only
        rw [dif_pos rfl]
        exact neg_add_cancel _
      have hs2 : s2.weightedVSub p f = (0 : V) := by
        set f2 : ι → V := fun x => f x • (p x -ᵥ p i1) with hf2def
        set g2 : { x // x ≠ i1 } → V := fun x => g x • (p x -ᵥ p i1)
        have hf2g2 : ∀ x : { x // x ≠ i1 }, f2 x = g2 x := by
          simp only [g2, hf2def]
          refine fun x => ?_
          rw [hfg]
        rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s2 f p hf (p i1),
          Finset.weightedVSubOfPoint_insert, Finset.weightedVSubOfPoint_apply,
          Finset.sum_subtype_map_embedding fun x _ => hf2g2 x]
        exact hg
      exact h s2 f hf hs2 i (Finset.mem_insert_of_mem (Finset.mem_map.2 ⟨i, hi, rfl⟩))
    · intro h
      rw [linearIndependent_iff'] at h
      intro s w hw hs i hi
      rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s w p hw (p i1), ←
        s.weightedVSubOfPoint_erase w p i1, Finset.weightedVSubOfPoint_apply] at hs
      let f : ι → V := fun i => w i • (p i -ᵥ p i1)
      have hs2 : (∑ i ∈ (s.erase i1).subtype fun i => i ≠ i1, f i) = 0 := by
        rw [← hs]
        convert Finset.sum_subtype_of_mem f fun x => Finset.ne_of_mem_erase
      have h2 := h ((s.erase i1).subtype fun i => i ≠ i1) (fun x => w x) hs2
      simp_rw [Finset.mem_subtype] at h2
      have h2b : ∀ i ∈ s, i ≠ i1 → w i = 0 := fun i his hi =>
        h2 ⟨i, hi⟩ (Finset.mem_erase_of_ne_of_mem hi his)
      exact Finset.eq_zero_of_sum_eq_zero hw h2b i hi

