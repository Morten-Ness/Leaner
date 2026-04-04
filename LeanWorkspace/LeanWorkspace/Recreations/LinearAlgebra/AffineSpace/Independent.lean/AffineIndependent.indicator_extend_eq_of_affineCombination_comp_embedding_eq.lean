import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

theorem AffineIndependent.indicator_extend_eq_of_affineCombination_comp_embedding_eq {ι₂ : Type*}
    {p : ι → P} (ha : AffineIndependent k p) {s₁ : Finset ι} {s₂ : Finset ι₂} {w₁ : ι → k}
    {w₂ : ι₂ → k} (hw₁ : ∑ i ∈ s₁, w₁ i = 1) (hw₂ : ∑ i ∈ s₂, w₂ i = 1) (e : ι₂ ↪ ι)
    (h : s₂.affineCombination k (p ∘ e) w₂ = s₁.affineCombination k p w₁) :
    Set.indicator (s₂.map e) (extend e w₂ 0) = Set.indicator s₁ w₁ := by
  have hw₂e : extend e w₂ 0 ∘ e = w₂ := extend_comp e.injective _ _
  rw [← hw₂e, ← affineCombination_map] at h
  refine (ha.indicator_eq_of_affineCombination_eq s₁ (s₂.map e) _ _ hw₁ ?_ h.symm).symm
  rw [sum_map]
  convert hw₂ with i hi
  exact e.injective.extend_apply _ _ _

