import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

theorem AffineIndependent.indicator_extend_eq_of_affineCombination_comp_embedding_eq_of_fintype
    [Fintype ι] {ι₂ : Type*} [Fintype ι₂] {p : ι → P} (ha : AffineIndependent k p) {w₁ : ι → k}
    {w₂ : ι₂ → k} (hw₁ : ∑ i, w₁ i = 1) (hw₂ : ∑ i, w₂ i = 1) (e : ι₂ ↪ ι)
    (h : Finset.univ.affineCombination k (p ∘ e) w₂ = Finset.univ.affineCombination k p w₁) :
    Set.indicator (Set.range e) (extend e w₂ 0) = w₁ := by
  simpa using ha.indicator_extend_eq_of_affineCombination_comp_embedding_eq hw₁ hw₂ e h

