import Mathlib

theorem AffineMap.homothety_mem {k V P : Type*} [CommRing k] [AddCommGroup V] [Module k V]
    [AddTorsor V P] {s : AffineSubspace k P} {c : P} (hc : c ∈ s) (r : k) {p : P} (hp : p ∈ s) :
    AffineMap.homothety c r p ∈ s := by
  rw [AffineMap.homothety_eq_lineMap]
  exact lineMap_mem r hc hp

