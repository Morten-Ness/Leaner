FAIL
import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem directionOfNonempty_eq_direction {s : AffineSubspace k P} (h : (s : Set P).Nonempty) :
    AffineSubspace.directionOfNonempty h = s.direction := by
  rcases h with ⟨p, hp⟩
  ext v
  constructor
  · rintro ⟨p1, hp1, p2, hp2, hv⟩
    rw [← hv]
    exact s.vsub_mem_direction hp1 hp2
  · intro hv
    refine ⟨(p +ᵥ v), ?_, p, hp, ?_⟩
    · exact s.mk'_mem_vadd hp hv
    · simp
