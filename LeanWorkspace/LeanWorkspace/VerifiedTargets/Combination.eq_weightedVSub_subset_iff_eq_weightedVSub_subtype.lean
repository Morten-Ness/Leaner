import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem eq_weightedVSub_subset_iff_eq_weightedVSub_subtype {v : V} {s : Set ι} {p : ι → P} :
    (∃ fs : Finset ι, ↑fs ⊆ s ∧ ∃ w : ι → k, ∑ i ∈ fs, w i = 0 ∧
        v = fs.weightedVSub p w) ↔
      ∃ (fs : Finset s) (w : s → k), ∑ i ∈ fs, w i = 0 ∧
        v = fs.weightedVSub (fun i : s => p i) w := Finset.eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype

