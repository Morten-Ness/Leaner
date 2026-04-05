import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable (s : Subring R)

theorem neg_mem {x : R} : x ∈ s → -x ∈ s := neg_mem

