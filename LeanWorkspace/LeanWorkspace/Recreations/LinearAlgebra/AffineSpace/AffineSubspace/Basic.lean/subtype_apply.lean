import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem subtype_apply {s : AffineSubspace k P} [Nonempty s] (p : s) : s.subtype p = p := rfl

