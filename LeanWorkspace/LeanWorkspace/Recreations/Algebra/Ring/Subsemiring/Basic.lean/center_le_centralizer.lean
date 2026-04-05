import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem center_le_centralizer {R} [Semiring R] (s) : Subsemiring.center R ≤ Subsemiring.centralizer s := s.center_subset_centralizer

