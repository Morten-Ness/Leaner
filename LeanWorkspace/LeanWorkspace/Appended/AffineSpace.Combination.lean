import Mathlib

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem affineCombination_apply_const (w : ι → k) (p : P) (h : ∑ i ∈ s, w i = 1) :
    s.affineCombination k (fun _ => p) w = p := by
  rw [Finset.affineCombination_apply, Finset.weightedVSubOfPoint_apply_const s, h, one_smul, vsub_vadd]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem affineCombination_congr {w₁ w₂ : ι → k} (hw : ∀ i ∈ s, w₁ i = w₂ i) {p₁ p₂ : ι → P}
    (hp : ∀ i ∈ s, p₁ i = p₂ i) : s.affineCombination k p₁ w₁ = s.affineCombination k p₂ w₂ := by
  simp_rw [Finset.affineCombination_apply, Finset.weightedVSubOfPoint_congr s hw hp]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem affineCombination_eq_linear_combination (s : Finset ι) (p : ι → V) (w : ι → k)
    (hw : ∑ i ∈ s, w i = 1) : s.affineCombination k p w = ∑ i ∈ s, w i • p i := by
  simp [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one s w p hw 0]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one (w : ι → k) (p : ι → P)
    (h : ∑ i ∈ s, w i = 1) (b : P) :
    s.affineCombination k p w = s.weightedVSubOfPoint p b w +ᵥ b := Finset.weightedVSubOfPoint_vadd_eq_of_sum_eq_one s w p h _ _

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem affineCombination_filter_of_ne (w : ι → k) (p : ι → P) {pred : ι → Prop}
    [DecidablePred pred] (h : ∀ i ∈ s, w i ≠ 0 → pred i) :
    {x ∈ s | pred x}.affineCombination k p w = s.affineCombination k p w := by
  rw [Finset.affineCombination_apply, Finset.affineCombination_apply,
    Finset.weightedVSubOfPoint_filter_of_ne s _ _ _ h]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem affineCombination_indicator_subset (w : ι → k) (p : ι → P) {s₁ s₂ : Finset ι}
    (h : s₁ ⊆ s₂) :
    s₁.affineCombination k p w = s₂.affineCombination k p (Set.indicator (↑s₁) w) := by
  rw [Finset.affineCombination_apply, Finset.affineCombination_apply,
    Finset.weightedVSubOfPoint_indicator_subset _ _ _ h]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem affineCombination_map (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) :
    (s₂.map e).affineCombination k p w = s₂.affineCombination k (p ∘ e) (w ∘ e) := by
  simp_rw [Finset.affineCombination_apply, Finset.weightedVSubOfPoint_map]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem affineCombination_sdiff_sub [DecidableEq ι] {s₂ : Finset ι} (h : s₂ ⊆ s) (w : ι → k)
    (p : ι → P) :
    (s \ s₂).affineCombination k p w -ᵥ s₂.affineCombination k p (-w) = s.weightedVSub p w := by
  simp_rw [Finset.affineCombination_apply, vadd_vsub_vadd_cancel_right]
  exact Finset.weightedVSub_sdiff_sub s h _ _

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem affineCombination_subtype_eq_filter (w : ι → k) (p : ι → P) (pred : ι → Prop)
    [DecidablePred pred] :
    ((s.subtype pred).affineCombination k (fun i => p i) fun i => w i) =
      {x ∈ s | pred x}.affineCombination k p w := by
  rw [Finset.affineCombination_apply, Finset.affineCombination_apply, Finset.weightedVSubOfPoint_subtype_eq_filter]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem affineCombination_vsub (w₁ w₂ : ι → k) (p : ι → P) :
    s.affineCombination k p w₁ -ᵥ s.affineCombination k p w₂ = s.weightedVSub p (w₁ - w₂) := by
  rw [← AffineMap.linearMap_vsub, Finset.affineCombination_linear, vsub_eq_sub]

end

section

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

end

section

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

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem sum_smul_const_vsub_eq_neg_weightedVSub (w : ι → k) (p₂ : ι → P) (p₁ : P)
    (h : ∑ i ∈ s, w i = 0) : (∑ i ∈ s, w i • (p₁ -ᵥ p₂ i)) = -s.weightedVSub p₂ w := by
  rw [Finset.sum_smul_vsub_eq_weightedVSub_sub, Finset.weightedVSub_apply_const s _ _ h, zero_sub]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem sum_smul_const_vsub_eq_sub_weightedVSubOfPoint (w : ι → k) (p₂ : ι → P) (p₁ b : P) :
    (∑ i ∈ s, w i • (p₁ -ᵥ p₂ i)) = (∑ i ∈ s, w i) • (p₁ -ᵥ b) - s.weightedVSubOfPoint p₂ b w := by
  rw [Finset.sum_smul_vsub_eq_weightedVSubOfPoint_sub, Finset.weightedVSubOfPoint_apply_const]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem sum_smul_const_vsub_eq_vsub_affineCombination (w : ι → k) (p₂ : ι → P) (p₁ : P)
    (h : ∑ i ∈ s, w i = 1) : (∑ i ∈ s, w i • (p₁ -ᵥ p₂ i)) = p₁ -ᵥ s.affineCombination k p₂ w := by
  rw [Finset.sum_smul_vsub_eq_affineCombination_vsub, Finset.affineCombination_apply_const _ _ _ h]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem sum_smul_vsub_const_eq_affineCombination_vsub (w : ι → k) (p₁ : ι → P) (p₂ : P)
    (h : ∑ i ∈ s, w i = 1) : (∑ i ∈ s, w i • (p₁ i -ᵥ p₂)) = s.affineCombination k p₁ w -ᵥ p₂ := by
  rw [Finset.sum_smul_vsub_eq_affineCombination_vsub, Finset.affineCombination_apply_const _ _ _ h]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem sum_smul_vsub_const_eq_weightedVSub (w : ι → k) (p₁ : ι → P) (p₂ : P)
    (h : ∑ i ∈ s, w i = 0) : (∑ i ∈ s, w i • (p₁ i -ᵥ p₂)) = s.weightedVSub p₁ w := by
  rw [Finset.sum_smul_vsub_eq_weightedVSub_sub, Finset.weightedVSub_apply_const s _ _ h, sub_zero]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem sum_smul_vsub_const_eq_weightedVSubOfPoint_sub (w : ι → k) (p₁ : ι → P) (p₂ b : P) :
    (∑ i ∈ s, w i • (p₁ i -ᵥ p₂)) = s.weightedVSubOfPoint p₁ b w - (∑ i ∈ s, w i) • (p₂ -ᵥ b) := by
  rw [Finset.sum_smul_vsub_eq_weightedVSubOfPoint_sub, Finset.weightedVSubOfPoint_apply_const]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem sum_smul_vsub_eq_affineCombination_vsub (w : ι → k) (p₁ p₂ : ι → P) :
    (∑ i ∈ s, w i • (p₁ i -ᵥ p₂ i)) =
      s.affineCombination k p₁ w -ᵥ s.affineCombination k p₂ w := by
  simp_rw [Finset.affineCombination_apply, vadd_vsub_vadd_cancel_right]
  exact Finset.sum_smul_vsub_eq_weightedVSubOfPoint_sub s _ _ _ _

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem sum_smul_vsub_eq_weightedVSub_sub (w : ι → k) (p₁ p₂ : ι → P) :
    (∑ i ∈ s, w i • (p₁ i -ᵥ p₂ i)) = s.weightedVSub p₁ w - s.weightedVSub p₂ w := Finset.sum_smul_vsub_eq_weightedVSubOfPoint_sub s _ _ _ _

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSubOfPoint_apply (w : ι → k) (p : ι → P) (b : P) :
    s.weightedVSubOfPoint p b w = ∑ i ∈ s, w i • (p i -ᵥ b) := by
  simp [Finset.weightedVSubOfPoint, LinearMap.sum_apply]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSubOfPoint_eq_of_weights_eq (p : ι → P) (j : ι) (w₁ w₂ : ι → k)
    (hw : ∀ i, i ≠ j → w₁ i = w₂ i) :
    s.weightedVSubOfPoint p (p j) w₁ = s.weightedVSubOfPoint p (p j) w₂ := by
  simp only [Finset.weightedVSubOfPoint_apply]
  congr
  ext i
  rcases eq_or_ne i j with h | h
  · simp [h]
  · simp [hw i h]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSubOfPoint_map (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) (b : P) :
    (s₂.map e).weightedVSubOfPoint p b w = s₂.weightedVSubOfPoint (p ∘ e) b (w ∘ e) := by
  simp_rw [Finset.weightedVSubOfPoint_apply]
  exact Finset.sum_map _ _ _

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSubOfPoint_sdiff_sub [DecidableEq ι] {s₂ : Finset ι} (h : s₂ ⊆ s) (w : ι → k)
    (p : ι → P) (b : P) :
    (s \ s₂).weightedVSubOfPoint p b w - s₂.weightedVSubOfPoint p b (-w) =
      s.weightedVSubOfPoint p b w := by
  rw [map_neg, sub_neg_eq_add, Finset.weightedVSubOfPoint_sdiff s h]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSubOfPoint_vadd (s : Finset ι) (w : ι → k) (p : ι → P) (b : P) (v : V) :
    s.weightedVSubOfPoint (v +ᵥ p) b w = s.weightedVSubOfPoint p (-v +ᵥ b) w := by
  simp [vadd_vsub_assoc, vsub_vadd_eq_vsub_sub, add_comm]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_apply_const (w : ι → k) (p : P) (h : ∑ i ∈ s, w i = 0) :
    s.weightedVSub (fun _ => p) w = 0 := by
  rw [Finset.weightedVSub, Finset.weightedVSubOfPoint_apply_const, h, zero_smul]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_congr {w₁ w₂ : ι → k} (hw : ∀ i ∈ s, w₁ i = w₂ i) {p₁ p₂ : ι → P}
    (hp : ∀ i ∈ s, p₁ i = p₂ i) : s.weightedVSub p₁ w₁ = s.weightedVSub p₂ w₂ := Finset.weightedVSubOfPoint_congr s hw hp _

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_const_smul (w : ι → k) (p : ι → P) (c : k) :
    s.weightedVSub p (c • w) = c • s.weightedVSub p w := Finset.weightedVSubOfPoint_const_smul s _ _ _ _

instance : AddTorsor (ι → k) (ι → k) := Pi.instAddTorsor

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_empty (w : ι → k) (p : ι → P) : (∅ : Finset ι).weightedVSub p w = (0 : V) := by
  simp [Finset.weightedVSub_apply]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem weightedVSub_eq_linear_combination {ι} (s : Finset ι) {w : ι → k} {p : ι → V}
    (hw : s.sum w = 0) : s.weightedVSub p w = ∑ i ∈ s, w i • p i := by
  simp [Finset.weightedVSub_apply s, vsub_eq_sub, smul_sub, ← Finset.sum_smul, hw]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero (w : ι → k) (p : ι → P)
    (h : ∑ i ∈ s, w i = 0) (b : P) : s.weightedVSub p w = s.weightedVSubOfPoint p b w := Finset.weightedVSubOfPoint_eq_of_sum_eq_zero s w p h _ _

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_filter_of_ne (w : ι → k) (p : ι → P) {pred : ι → Prop} [DecidablePred pred]
    (h : ∀ i ∈ s, w i ≠ 0 → pred i) : {x ∈ s | pred x}.weightedVSub p w = s.weightedVSub p w := Finset.weightedVSubOfPoint_filter_of_ne s _ _ _ h

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_indicator_subset (w : ι → k) (p : ι → P) {s₁ s₂ : Finset ι} (h : s₁ ⊆ s₂) :
    s₁.weightedVSub p w = s₂.weightedVSub p (Set.indicator (↑s₁) w) := Finset.weightedVSubOfPoint_indicator_subset _ _ _ h

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_map (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) :
    (s₂.map e).weightedVSub p w = s₂.weightedVSub (p ∘ e) (w ∘ e) := Finset.weightedVSubOfPoint_map s₂ _ _ _ _

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_sdiff [DecidableEq ι] {s₂ : Finset ι} (h : s₂ ⊆ s) (w : ι → k) (p : ι → P) :
    (s \ s₂).weightedVSub p w + s₂.weightedVSub p w = s.weightedVSub p w := Finset.weightedVSubOfPoint_sdiff s h _ _ _

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_sdiff_sub [DecidableEq ι] {s₂ : Finset ι} (h : s₂ ⊆ s) (w : ι → k)
    (p : ι → P) : (s \ s₂).weightedVSub p w - s₂.weightedVSub p (-w) = s.weightedVSub p w := Finset.weightedVSubOfPoint_sdiff_sub s h _ _ _

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_smul {G : Type*} [Group G] [DistribMulAction G V] [SMulCommClass G k V]
    {s : Finset ι} {w : ι → k} (h : ∑ i ∈ s, w i = 0) (p : ι → V) (a : G) :
    s.weightedVSub (a • p) w = a • s.weightedVSub p w := by
  rw [Finset.weightedVSub, Finset.weightedVSubOfPoint_smul,
    Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ h]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_subtype_eq_filter (w : ι → k) (p : ι → P) (pred : ι → Prop)
    [DecidablePred pred] :
    ((s.subtype pred).weightedVSub (fun i => p i) fun i => w i) =
      {x ∈ s | pred x}.weightedVSub p w := Finset.weightedVSubOfPoint_subtype_eq_filter s _ _ _ _

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_vadd {s : Finset ι} {w : ι → k} (h : ∑ i ∈ s, w i = 0) (p : ι → P) (v : V) :
    s.weightedVSub (v +ᵥ p) w = s.weightedVSub p w := by
  rw [Finset.weightedVSub, Finset.weightedVSubOfPoint_vadd,
    Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ h]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

variable (k)

variable {k}

theorem weightedVSub_vadd_affineCombination (w₁ w₂ : ι → k) (p : ι → P) :
    s.weightedVSub p w₁ +ᵥ s.affineCombination k p w₂ = s.affineCombination k p (w₁ + w₂) := by
  rw [← vadd_eq_add, AffineMap.map_vadd, Finset.affineCombination_linear]

end
