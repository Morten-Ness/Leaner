import Mathlib

variable (R : Type*) [CommRing R]

variable {P : RingPreordering R}

theorem hasIdealSupport_iff :
    P.HasIdealSupport ↔ ∀ x a : R, a ∈ P → -a ∈ P → x * a ∈ P ∧ -(x * a) ∈ P where
  mp _ := by simpa [RingPreordering.mem_supportAddSubgroup] using P.smul_mem_support
  mpr _ := ⟨by simpa [RingPreordering.mem_supportAddSubgroup]⟩

