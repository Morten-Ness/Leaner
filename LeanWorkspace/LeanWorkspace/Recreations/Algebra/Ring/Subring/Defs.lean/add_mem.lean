import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable (s : Subring R)

theorem add_mem {x y : R} : x ∈ s → y ∈ s → x + y ∈ s := add_mem

