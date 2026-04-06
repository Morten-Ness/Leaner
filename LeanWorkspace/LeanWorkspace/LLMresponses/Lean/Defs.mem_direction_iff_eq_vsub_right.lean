FAIL
import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem mem_direction_iff_eq_vsub_right {s : AffineSubspace k P} {p : P} (hp : p ∈ s) (v : V) :
    v ∈ s.direction ↔ ∃ p₂ ∈ s, v = p₂ -ᵥ p := by
  constructor
  · intro hv
    refine ⟨v +ᵥ p, s.smul_vsub_vadd_mem ?_ hp, ?_⟩
    · simpa using hv
    · simp
  · rintro ⟨p₂, hp₂, rfl⟩
    exact s.vsub_mem_direction hp₂ hp
