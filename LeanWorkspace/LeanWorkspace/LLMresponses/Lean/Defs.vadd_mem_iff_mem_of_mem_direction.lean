FAIL
import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem vadd_mem_iff_mem_of_mem_direction {s : AffineSubspace k P} {v : V} (hv : v ∈ s.direction)
    {p : P} : v +ᵥ p ∈ s ↔ p ∈ s := by
  constructor
  · intro hp
    have hmem : p -ᵥ (v +ᵥ p) ∈ s.direction := by
      rw [s.vsub_right_mem_direction_iff_mem hp]
      exact hp
    simpa using hmem
  · intro hp
    have hmem : (v +ᵥ p) -ᵥ p ∈ s.direction := by
      simpa using hv
    exact s.vadd_vsub_mem_of_mem_direction hmem hp
