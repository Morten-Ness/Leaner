import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable (s : Subring R)

theorem coe_toAddSubgroup (s : Subring R) : (s.toAddSubgroup : Set R) = s := rfl

