FAIL
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
        v = fs.weightedVSub (fun i : s => p i) w := by
  classical
  constructor
  · rintro ⟨fs, hfs, w, hw, hv⟩
    let fs' : Finset s := fs.attach.map
      { toFun := fun i => ⟨i.1, hfs i.2⟩
        inj' := by
          intro a b h
          exact Subtype.ext h }
    refine ⟨fs', fun i => w i.1, ?_, ?_⟩
    · unfold fs'
      simpa using hw
    · unfold fs'
      simpa using hv
  · rintro ⟨fs, w, hw, hv⟩
    refine ⟨fs.image (fun i : s => (i : ι)), ?_, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
      exact j.2
    · let w' : ι → k := fun i => if h : i ∈ s then w ⟨i, h⟩ else 0
      refine ⟨w', ?_, ?_⟩
      · unfold w'
        rw [Finset.sum_image]
        · simpa using hw
        · intro a _ b _ hab
          exact Subtype.ext hab
      · unfold w'
        rw [Finset.weightedVSub_image]
        · simpa using hv
        · intro a _ b _ hab
          exact Subtype.ext hab
