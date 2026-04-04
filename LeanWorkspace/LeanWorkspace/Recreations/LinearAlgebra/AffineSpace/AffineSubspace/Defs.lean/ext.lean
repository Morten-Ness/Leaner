import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem ext {p q : AffineSubspace k P} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

