import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*} (s : Finset ι) {ι₂ : Type*} (s₂ : Finset ι₂)

variable {k} in

theorem centroid_map (e : ι₂ ↪ ι) (p : ι → P) :
    (s₂.map e).centroid k p = s₂.centroid k (p ∘ e) := by
  simp [Finset.centroid_def, affineCombination_map, Finset.centroidWeights]

