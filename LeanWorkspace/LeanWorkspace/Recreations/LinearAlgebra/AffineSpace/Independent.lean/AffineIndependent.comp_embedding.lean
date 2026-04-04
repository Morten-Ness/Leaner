import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

theorem AffineIndependent.comp_embedding {ι2 : Type*} (f : ι2 ↪ ι) {p : ι → P}
    (ha : AffineIndependent k p) : AffineIndependent k (p ∘ f) := by
  classical
    intro fs w hw hs i0 hi0
    let fs' := fs.map f
    let w' i := if h : ∃ i2, f i2 = i then w h.choose else 0
    have hw' : ∀ i2 : ι2, w' (f i2) = w i2 := by
      intro i2
      have h : ∃ i : ι2, f i = f i2 := ⟨i2, rfl⟩
      have hs : h.choose = i2 := f.injective h.choose_spec
      simp_rw [w', dif_pos h, hs]
    have hw's : ∑ i ∈ fs', w' i = 0 := by
      rw [← hw, Finset.sum_map]
      simp [hw']
    have hs' : fs'.weightedVSub p w' = (0 : V) := by
      rw [← hs, Finset.weightedVSub_map]
      congr with i
      simp_all only [comp_apply]
    rw [← ha fs' w' hw's hs' (f i0) ((Finset.mem_map' _).2 hi0), hw']

