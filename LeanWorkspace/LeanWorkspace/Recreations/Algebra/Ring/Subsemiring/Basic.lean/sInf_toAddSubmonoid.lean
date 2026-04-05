import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem sInf_toAddSubmonoid (s : Set (Subsemiring R)) :
    (sInf s).toAddSubmonoid = ⨅ t ∈ s, Subsemiring.toAddSubmonoid t := mk'_toAddSubmonoid _ _

