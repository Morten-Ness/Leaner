import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem inclusion_injective {S T : Subring R} (h : S ≤ T) :
    Function.Injective (Subring.inclusion h) := RingHom.injective_codRestrict.mpr S.subtype_injective

