import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem vadd_mem_iff_mem_direction {s : AffineSubspace k P} (v : V) {p : P} (hp : p ∈ s) :
    v +ᵥ p ∈ s ↔ v ∈ s.direction := ⟨fun h => by simpa using AffineSubspace.vsub_mem_direction h hp, fun h => AffineSubspace.vadd_mem_of_mem_direction h hp⟩

