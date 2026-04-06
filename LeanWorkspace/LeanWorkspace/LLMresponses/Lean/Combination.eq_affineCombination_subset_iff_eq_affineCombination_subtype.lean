FAIL
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
  classical
  constructor
  · rintro ⟨fs, hsub, w, hsum, hp0⟩
    refine ⟨fs.attach.image (fun i => (⟨i.1, hsub i.2⟩ : s)), fun i => w i.1, ?_, ?_⟩
    · classical
      have hinj :
          Function.Injective (fun i : {x // x ∈ fs} => (⟨i.1, hsub i.2⟩ : s)) := by
        intro a b h
        exact Subtype.ext h.1
      rw [← Finset.sum_attach (s := fs) (f := fun i => w i)]
      simpa [Finset.sum_image, hinj]
    · rw [hp0]
      have hinj :
          Function.Injective (fun i : {x // x ∈ fs} => (⟨i.1, hsub i.2⟩ : s)) := by
        intro a b h
        exact Subtype.ext h.1
      rw [← Finset.affineCombination_map
        (f := Embedding.ofInjective (fun i : {x // x ∈ fs} => (⟨i.1, hsub i.2⟩ : s)) hinj)
        (p := fun i : s => p i) (w := fun i : s => w i.1)]
      simp [Finset.attach_image_val]
  · rintro ⟨fs, w, hsum, hp0⟩
    refine ⟨fs.image Subtype.val, ?_, (fun i => if h : i ∈ s then w ⟨i, h⟩ else 0), ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
      exact j.2
    · have hnodup : (fs : Finset ι).Nodup := fs.nodup.map ⟨Subtype.val, by intro a b h; exact Subtype.ext h⟩
      rw [Finset.sum_image]
      · refine Finset.sum_congr rfl ?_
        intro i hi
        simp
      · intro a ha b hb hab
        exact Subtype.ext hab
    · rw [← hp0]
      have hinj : Function.Injective (fun x : s => (x : ι)) := fun _ _ h => Subtype.ext h
      rw [Finset.affineCombination_image
        (f := Embedding.ofInjective (fun x : s => (x : ι)) hinj)
        (p := p) (w := fun i => if h : i ∈ s then w ⟨i, h⟩ else 0)]
      · refine Finset.affineCombination_congr ?_ ?_
        · intro i hi
          simp
        · intro i hi
          simp [i.2]
      · intro a ha b hb hab
        exact Subtype.ext hab
