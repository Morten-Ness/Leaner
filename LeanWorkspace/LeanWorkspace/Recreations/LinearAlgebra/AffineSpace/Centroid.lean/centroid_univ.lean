import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*} (s : Finset ι) {ι₂ : Type*} (s₂ : Finset ι₂)

variable {k} in

theorem centroid_univ (s : Finset P) : univ.centroid k ((↑) : s → P) = s.centroid k id := by
  rw [Finset.centroid, Finset.centroid, ← s.attach_affineCombination_coe]
  congr
  ext
  simp

