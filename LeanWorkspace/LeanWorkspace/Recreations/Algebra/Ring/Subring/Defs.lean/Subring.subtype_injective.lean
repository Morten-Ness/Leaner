import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable (s : Subring R)

theorem subtype_injective (s : Subring R) :
    Function.Injective s.subtype := SubringClass.subtype_injective s.toSubmonoid

