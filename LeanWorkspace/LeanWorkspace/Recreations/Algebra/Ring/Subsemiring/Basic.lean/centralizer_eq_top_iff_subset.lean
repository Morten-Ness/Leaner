import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem centralizer_eq_top_iff_subset {R} [Semiring R] {s : Set R} :
    Subsemiring.centralizer s = ⊤ ↔ s ⊆ Subsemiring.center R := SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

