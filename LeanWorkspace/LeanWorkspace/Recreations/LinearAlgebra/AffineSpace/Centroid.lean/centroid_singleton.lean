import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*} (s : Finset ι) {ι₂ : Type*} (s₂ : Finset ι₂)

variable {k} in

theorem centroid_singleton (p : ι → P) (i : ι) : ({i} : Finset ι).centroid k p = p i := by
  simp [Finset.centroid_def, affineCombination_apply]

