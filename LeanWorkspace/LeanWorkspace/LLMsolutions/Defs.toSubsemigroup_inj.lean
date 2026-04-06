import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

theorem toSubsemigroup_inj {s t : Submonoid M} : s.toSubsemigroup = t.toSubsemigroup ↔ s = t := by
  constructor
  · intro h
    ext x
    change x ∈ s.toSubsemigroup ↔ x ∈ t.toSubsemigroup
    rw [h]
  · intro h
    rw [h]
