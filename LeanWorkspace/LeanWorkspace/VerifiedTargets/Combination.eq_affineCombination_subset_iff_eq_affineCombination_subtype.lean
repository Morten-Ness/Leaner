import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

variable (V)

theorem eq_affineCombination_subset_iff_eq_affineCombination_subtype {p0 : P} {s : Set ι}
    {p : ι → P} :
    (∃ fs : Finset ι, ↑fs ⊆ s ∧ ∃ w : ι → k, ∑ i ∈ fs, w i = 1 ∧
        p0 = fs.affineCombination k p w) ↔
      ∃ (fs : Finset s) (w : s → k), ∑ i ∈ fs, w i = 1 ∧
        p0 = fs.affineCombination k (fun i : s => p i) w := by
  simp_rw [Finset.affineCombination_apply, eq_vadd_iff_vsub_eq]
  exact Finset.eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype

