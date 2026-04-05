import Mathlib

variable {F α β R S S' : Type*}

variable [NonAssocRing R] [NonAssocRing S] (f : R ≃+* S)

theorem map_eq_neg_one_iff {x : R} : f x = -1 ↔ x = -1 := by
  rw [← neg_eq_iff_eq_neg, ← neg_eq_iff_eq_neg, ← RingEquiv.map_neg, RingEquiv.map_eq_one_iff]

