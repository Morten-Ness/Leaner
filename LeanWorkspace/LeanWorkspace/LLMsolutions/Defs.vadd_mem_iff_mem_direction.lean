FAIL
import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem vadd_mem_iff_mem_direction {s : AffineSubspace k P} (v : V) {p : P} (hp : p ∈ s) :
    v +ᵥ p ∈ s ↔ v ∈ s.direction := by
  constructor
  · intro hv
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hp hv]
    simp
  · intro hv
    rw [← AffineSubspace.mem_direction_iff_eq_vsub_right hp]
    simpa using hv
