import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem le_centralizer_centralizer {R} [Semiring R] {s : Subsemiring R} :
    s ≤ Subsemiring.centralizer (Subsemiring.centralizer (s : Set R)) := Set.subset_centralizer_centralizer

