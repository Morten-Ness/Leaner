import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem mk'_nonempty (p : P) (AffineSubspace.direction : Submodule k V) : (AffineSubspace.mk' p AffineSubspace.direction : Set P).Nonempty := ⟨p, AffineSubspace.self_mem_mk' p AffineSubspace.direction⟩

instance (p : P) (AffineSubspace.direction : Submodule k V) : Nonempty (AffineSubspace.mk' p AffineSubspace.direction) :=
  ⟨⟨p, AffineSubspace.self_mem_mk' p AffineSubspace.direction⟩⟩

