import Mathlib

variable {R : Type*} [CommRing R] {P : RingPreordering R}

variable {F : Type*} [Field F] (P : RingPreordering F)

theorem supportAddSubgroup_eq_bot : P.supportAddSubgroup = ⊥ := by
  ext; aesop (add simp mem_supportAddSubgroup)

