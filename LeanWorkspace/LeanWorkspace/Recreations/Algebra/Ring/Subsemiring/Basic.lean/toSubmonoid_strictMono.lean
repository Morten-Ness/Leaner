import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable (s : Subsemiring R)

theorem toSubmonoid_strictMono : StrictMono (toSubmonoid : Subsemiring R → Submonoid R) := fun _ _ => id

