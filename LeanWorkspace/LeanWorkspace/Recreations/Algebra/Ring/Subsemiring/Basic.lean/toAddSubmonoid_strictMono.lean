import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable (s : Subsemiring R)

theorem toAddSubmonoid_strictMono : StrictMono (toAddSubmonoid : Subsemiring R → AddSubmonoid R) := fun _ _ => id

