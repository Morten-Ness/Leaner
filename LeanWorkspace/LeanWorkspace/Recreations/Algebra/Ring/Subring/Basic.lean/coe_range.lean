import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable (g : S →+* T) (f : R →+* S)

theorem coe_range : (f.range : Set S) = Set.range f := rfl

