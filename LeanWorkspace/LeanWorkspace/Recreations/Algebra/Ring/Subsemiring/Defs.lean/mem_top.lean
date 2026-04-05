import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

variable (s : Subsemiring R)

theorem mem_top (x : R) : x ∈ (⊤ : Subsemiring R) := Set.mem_univ x

