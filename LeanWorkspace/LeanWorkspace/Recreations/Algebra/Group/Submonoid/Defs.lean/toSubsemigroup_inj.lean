import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

theorem toSubsemigroup_inj {s t : Submonoid M} : s.toSubsemigroup = t.toSubsemigroup ↔ s = t := Submonoid.toSubsemigroup_injective.eq_iff

