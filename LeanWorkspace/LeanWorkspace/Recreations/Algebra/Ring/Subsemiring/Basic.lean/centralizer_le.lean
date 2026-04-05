import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem centralizer_le {R} [Semiring R] (s t : Set R) (h : s ⊆ t) : Subsemiring.centralizer t ≤ Subsemiring.centralizer s := Set.centralizer_subset h

