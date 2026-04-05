import Mathlib

variable {R : Type v} [NonAssocSemiring R] [StarRing R]

theorem toSubsemiring_inj {S U : StarSubsemiring R} : S.toSubsemiring = U.toSubsemiring ↔ S = U := StarSubsemiring.toSubsemiring_injective.eq_iff

