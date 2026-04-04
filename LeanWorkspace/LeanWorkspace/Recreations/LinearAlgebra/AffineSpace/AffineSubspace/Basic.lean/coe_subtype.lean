import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem coe_subtype (s : AffineSubspace k P) [Nonempty s] : (s.subtype : s → P) = ((↑) : s → P) := rfl

