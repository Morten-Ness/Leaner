import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem self_mem_mk' (p : P) (AffineSubspace.direction : Submodule k V) : p ∈ AffineSubspace.mk' p AffineSubspace.direction := by
  simp

