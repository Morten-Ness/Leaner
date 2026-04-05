import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem subsemiringClosure_mem {x : R} :
    x ∈ M.subsemiringClosure ↔ x ∈ AddSubmonoid.closure (M : Set R) := Iff.rfl

