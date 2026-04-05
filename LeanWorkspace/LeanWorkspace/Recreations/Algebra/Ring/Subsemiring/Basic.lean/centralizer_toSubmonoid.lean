import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem centralizer_toSubmonoid {R} [Semiring R] (s : Set R) :
    (Subsemiring.centralizer s).toSubmonoid = Submonoid.centralizer s := rfl

