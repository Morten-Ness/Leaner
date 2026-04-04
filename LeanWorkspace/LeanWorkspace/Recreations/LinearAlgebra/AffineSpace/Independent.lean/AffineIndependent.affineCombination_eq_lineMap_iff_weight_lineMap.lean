import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

variable {s : Finset ι} {w w₁ w₂ : ι → k} {p : ι → V}

theorem AffineIndependent.affineCombination_eq_lineMap_iff_weight_lineMap {p : ι → P}
    (ha : AffineIndependent k p) {w w₁ w₂ : ι → k} {s : Finset ι} (hw : ∑ i ∈ s, w i = 1)
    (hw₁ : ∑ i ∈ s, w₁ i = 1) (hw₂ : ∑ i ∈ s, w₂ i = 1) (c : k) :
    s.affineCombination k p w =
      AffineMap.lineMap (s.affineCombination k p w₁) (s.affineCombination k p w₂) c ↔
        ∀ i ∈ s, w i = AffineMap.lineMap (w₁ i) (w₂ i) c := by
  rw [← AffineMap.apply_lineMap, ha.affineCombination_eq_iff_eq hw]
  · simp [AffineMap.lineMap_apply]
  · simp [AffineMap.lineMap_apply, sum_add_distrib, ← mul_sum, hw₁, hw₂]

