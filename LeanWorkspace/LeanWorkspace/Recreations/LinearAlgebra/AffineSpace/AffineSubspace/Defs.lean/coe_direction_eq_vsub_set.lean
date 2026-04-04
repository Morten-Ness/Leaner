import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem coe_direction_eq_vsub_set {s : AffineSubspace k P} (h : (s : Set P).Nonempty) :
    (s.direction : Set V) = (s : Set P) -ᵥ s := AffineSubspace.directionOfNonempty_eq_direction h ▸ rfl

