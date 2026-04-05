import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem center_eq_top (R) [CommSemiring R] : Subsemiring.center R = ⊤ := SetLike.coe_injective (Set.center_eq_univ R)

