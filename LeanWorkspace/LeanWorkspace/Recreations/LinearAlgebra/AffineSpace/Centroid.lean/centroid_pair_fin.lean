import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*} (s : Finset ι) {ι₂ : Type*} (s₂ : Finset ι₂)

variable {k} in

theorem centroid_pair_fin [Invertible (2 : k)] (p : Fin 2 → P) :
    univ.centroid k p = (2⁻¹ : k) • (p 1 -ᵥ p 0) +ᵥ p 0 := by
  rw [univ_fin2]
  convert Finset.centroid_pair k p 0 1

