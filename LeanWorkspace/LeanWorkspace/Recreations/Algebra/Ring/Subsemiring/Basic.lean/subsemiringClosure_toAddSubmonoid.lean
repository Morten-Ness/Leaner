import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem subsemiringClosure_toAddSubmonoid :
    M.subsemiringClosure.toAddSubmonoid = AddSubmonoid.closure (M : Set R) := rfl

