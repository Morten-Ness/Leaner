FAIL
import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem coe_direction_eq_vsub_set_right {s : AffineSubspace k P} {p : P} (hp : p ∈ s) :
    (s.direction : Set V) = (· -ᵥ p) '' s := by
  ext v
  constructor
  · intro hv
    rcases (AffineSubspace.mem_direction_iff_eq_vsub_right hp).mp hv with ⟨q, hq, rfl⟩
    exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact (AffineSubspace.mem_direction_iff_eq_vsub_right hp).2 ⟨q, hq, rfl⟩
