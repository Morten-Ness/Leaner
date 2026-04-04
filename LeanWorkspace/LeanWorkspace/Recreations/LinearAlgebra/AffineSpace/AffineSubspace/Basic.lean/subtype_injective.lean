import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem subtype_injective (s : AffineSubspace k P) [Nonempty s] : Function.Injective s.subtype := Subtype.coe_injective

