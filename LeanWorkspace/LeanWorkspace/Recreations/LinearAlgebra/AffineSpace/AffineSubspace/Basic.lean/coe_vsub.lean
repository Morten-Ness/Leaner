import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem coe_vsub (s : AffineSubspace k P) [Nonempty s] (a b : s) : ↑(a -ᵥ b) = (a : P) -ᵥ (b : P) := rfl

