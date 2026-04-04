import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem mem_direction_iff_eq_vsub_right {s : AffineSubspace k P} {p : P} (hp : p ∈ s) (v : V) :
    v ∈ s.direction ↔ ∃ p₂ ∈ s, v = p₂ -ᵥ p := by
  rw [← SetLike.mem_coe, AffineSubspace.coe_direction_eq_vsub_set_right hp]
  exact ⟨fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩, fun ⟨p₂, hp₂, hv⟩ => ⟨p₂, hp₂, hv.symm⟩⟩

