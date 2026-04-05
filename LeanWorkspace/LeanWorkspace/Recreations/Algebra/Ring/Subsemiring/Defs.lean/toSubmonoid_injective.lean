import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

theorem toSubmonoid_injective : Function.Injective (toSubmonoid : Subsemiring R → Submonoid R)
  | _, _, h => Subsemiring.ext (SetLike.ext_iff.mp h :)
