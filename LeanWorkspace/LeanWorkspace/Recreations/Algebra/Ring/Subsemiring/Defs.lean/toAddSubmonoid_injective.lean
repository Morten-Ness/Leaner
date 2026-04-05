import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

theorem toAddSubmonoid_injective :
    Function.Injective (toAddSubmonoid : Subsemiring R → AddSubmonoid R)
  | _, _, h => Subsemiring.ext (SetLike.ext_iff.mp h :)
