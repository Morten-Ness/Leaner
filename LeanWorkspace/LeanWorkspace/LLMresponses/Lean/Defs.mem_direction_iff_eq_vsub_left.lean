FAIL
import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem mem_direction_iff_eq_vsub_left {s : AffineSubspace k P} {p : P} (hp : p ∈ s) (v : V) :
    v ∈ s.direction ↔ ∃ p₂ ∈ s, v = p -ᵥ p₂ := by
  constructor
  · intro hv
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hp] at hv
    rcases hv with ⟨p₂, hp₂, h⟩
    refine ⟨p₂, hp₂, ?_⟩
    rw [h]
    exact neg_vsub_eq_vsub_rev p₂ p
  · rintro ⟨p₂, hp₂, h⟩
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hp]
    refine ⟨p₂, hp₂, ?_⟩
    rw [h]
    exact neg_vsub_eq_vsub_rev p p₂
