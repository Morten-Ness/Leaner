import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem direction_eq_vectorSpan (s : AffineSubspace k P) : s.direction = vectorSpan k (s : Set P) := rfl

