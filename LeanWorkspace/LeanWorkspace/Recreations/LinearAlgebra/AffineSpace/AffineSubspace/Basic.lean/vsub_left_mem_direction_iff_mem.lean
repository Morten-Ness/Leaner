import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem vsub_left_mem_direction_iff_mem {s : AffineSubspace k P} {p : P} (hp : p ∈ s) (p₂ : P) :
    p -ᵥ p₂ ∈ s.direction ↔ p₂ ∈ s := by
  rw [mem_direction_iff_eq_vsub_left hp]
  simp

