import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [S : AddTorsor V P]

variable {ι : Type*} (s : Finset ι)

variable {ι₂ : Type*} (s₂ : Finset ι₂)

theorem weightedVSub_indicator_subset (w : ι → k) (p : ι → P) {s₁ s₂ : Finset ι} (h : s₁ ⊆ s₂) :
    s₁.weightedVSub p w = s₂.weightedVSub p (Set.indicator (↑s₁) w) := Finset.weightedVSubOfPoint_indicator_subset _ _ _ h

