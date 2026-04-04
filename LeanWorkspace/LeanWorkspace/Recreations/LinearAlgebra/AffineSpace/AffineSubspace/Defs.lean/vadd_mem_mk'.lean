import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem vadd_mem_mk' {v : V} (p : P) {AffineSubspace.direction : Submodule k V} (hv : v ∈ AffineSubspace.direction) :
    v +ᵥ p ∈ AffineSubspace.mk' p AffineSubspace.direction := by
  simpa

