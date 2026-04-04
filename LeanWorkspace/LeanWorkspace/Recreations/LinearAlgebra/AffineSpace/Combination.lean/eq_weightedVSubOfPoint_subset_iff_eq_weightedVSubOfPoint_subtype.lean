import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem eq_weightedVSubOfPoint_subset_iff_eq_weightedVSubOfPoint_subtype {v : V} {x : k} {s : Set ι}
    {p : ι → P} {b : P} :
    (∃ fs : Finset ι, ↑fs ⊆ s ∧ ∃ w : ι → k, ∑ i ∈ fs, w i = x ∧
        v = fs.weightedVSubOfPoint p b w) ↔
      ∃ (fs : Finset s) (w : s → k), ∑ i ∈ fs, w i = x ∧
        v = fs.weightedVSubOfPoint (fun i : s => p i) b w := by
  classical
    simp_rw [Finset.weightedVSubOfPoint_apply]
    constructor
    · rintro ⟨fs, hfs, w, rfl, rfl⟩
      exact ⟨fs.subtype (· ∈ s), fun i => w i, sum_subtype_of_mem _ hfs,
        (sum_subtype_of_mem _ hfs).symm⟩
    · rintro ⟨fs, w, rfl, rfl⟩
      refine ⟨fs.map (Function.Embedding.subtype _), map_subtype_subset _, fun i =>
        if h : i ∈ s then w ⟨i, h⟩ else 0, ?_, ?_⟩ <;> simp

