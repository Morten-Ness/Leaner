import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem mk'_eq {s : AffineSubspace k P} {p : P} (hp : p ∈ s) : AffineSubspace.mk' p s.direction = s := AffineSubspace.ext_of_direction_eq (AffineSubspace.direction_mk' p s.direction) ⟨p, Set.mem_inter (AffineSubspace.self_mem_mk' _ _) hp⟩

