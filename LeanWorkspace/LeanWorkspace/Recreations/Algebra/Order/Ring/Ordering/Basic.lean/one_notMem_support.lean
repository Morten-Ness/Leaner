import Mathlib

variable {R : Type*} [CommRing R] {P : RingPreordering R}

theorem one_notMem_support [P.HasIdealSupport] : 1 ∉ P.support := by
  simpa using RingPreordering.one_notMem_supportAddSubgroup P

