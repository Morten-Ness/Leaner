import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem coe_injective : Function.Injective ((↑) : AffineSubspace k P → Set P) := SetLike.coe_injective

