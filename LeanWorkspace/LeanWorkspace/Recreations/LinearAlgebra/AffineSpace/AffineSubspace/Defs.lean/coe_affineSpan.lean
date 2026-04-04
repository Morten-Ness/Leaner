import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

theorem coe_affineSpan (s : Set P) : (affineSpan k s : Set P) = spanPoints k s := rfl

