import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem centralizer_univ {R} [Semiring R] : Subsemiring.centralizer Set.univ = Subsemiring.center R := SetLike.ext' (Set.centralizer_univ R)

