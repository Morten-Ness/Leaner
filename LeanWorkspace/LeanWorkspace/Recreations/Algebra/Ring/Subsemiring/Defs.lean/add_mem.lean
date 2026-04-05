import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

variable (s : Subsemiring R)

theorem add_mem {x y : R} : x ∈ s → y ∈ s → x + y ∈ s := add_mem

