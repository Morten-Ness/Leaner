FAIL
import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem coe_direction_eq_vsub_set_left {s : AffineSubspace k P} {p : P} (hp : p ∈ s) :
    (s.direction : Set V) = (p -ᵥ ·) '' s := by
  ext v
  constructor
  · intro hv
    refine ⟨v +ᵥ p, ?_, ?_⟩
    · simpa [add_comm] using s.vadd_mem_of_mem_direction hv hp
    · rw [vsub_vadd]
  · rintro ⟨q, hq, rfl⟩
    exact s.vsub_mem_direction hp hq
