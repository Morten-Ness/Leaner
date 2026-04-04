import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem mem_mk' {p q : P} {AffineSubspace.direction : Submodule k V} : q ∈ AffineSubspace.mk' p AffineSubspace.direction ↔ q -ᵥ p ∈ AffineSubspace.direction := Iff.rfl

