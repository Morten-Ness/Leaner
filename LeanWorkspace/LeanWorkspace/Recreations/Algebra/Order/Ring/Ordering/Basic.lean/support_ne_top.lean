import Mathlib

variable {R : Type*} [CommRing R] {P : RingPreordering R}

theorem support_ne_top [P.HasIdealSupport] : P.support ≠ ⊤ := by
  apply_fun Submodule.toAddSubgroup
  simpa using RingPreordering.supportAddSubgroup_ne_top P

