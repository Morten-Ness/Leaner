import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

variable (s : Subsemiring R)

theorem mul_mem {x y : R} : x ∈ s → y ∈ s → x * y ∈ s := mul_mem

