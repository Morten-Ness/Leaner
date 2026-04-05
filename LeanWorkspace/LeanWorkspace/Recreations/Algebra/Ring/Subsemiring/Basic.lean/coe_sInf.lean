import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem coe_sInf (S : Set (Subsemiring R)) : ((sInf S : Subsemiring R) : Set R) = ⋂ s ∈ S, ↑s := rfl

