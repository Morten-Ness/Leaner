FAIL
import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem coe_direction_eq_vsub_set {s : AffineSubspace k P} (h : (s : Set P).Nonempty) :
    (s.direction : Set V) = (s : Set P) -ᵥ s := by
  ext v
  constructor
  · intro hv
    rcases h with ⟨p, hp⟩
    refine ⟨p, hp, v +ᵥ p, ?_, by simp⟩
    exact s.vadd_mem_of_mem_direction hp hv
  · rintro ⟨p1, hp1, p2, hp2, hEq⟩
    rw [← hEq]
    exact s.vsub_mem_direction hp1 hp2
