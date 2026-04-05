import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem inclusion_injective {S T : Subsemiring R} (h : S ≤ T) :
    Function.Injective (Subsemiring.inclusion h) := Set.inclusion_injective h

