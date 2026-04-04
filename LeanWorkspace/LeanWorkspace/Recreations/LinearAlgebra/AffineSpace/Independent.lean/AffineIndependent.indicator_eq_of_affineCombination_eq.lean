import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

theorem AffineIndependent.indicator_eq_of_affineCombination_eq {p : ι → P}
    (ha : AffineIndependent k p) (s₁ s₂ : Finset ι) (w₁ w₂ : ι → k) (hw₁ : ∑ i ∈ s₁, w₁ i = 1)
    (hw₂ : ∑ i ∈ s₂, w₂ i = 1) (h : s₁.affineCombination k p w₁ = s₂.affineCombination k p w₂) :
    Set.indicator (↑s₁) w₁ = Set.indicator (↑s₂) w₂ := (affineIndependent_iff_indicator_eq_of_affineCombination_eq k p).1 ha s₁ s₂ w₁ w₂ hw₁ hw₂ h

