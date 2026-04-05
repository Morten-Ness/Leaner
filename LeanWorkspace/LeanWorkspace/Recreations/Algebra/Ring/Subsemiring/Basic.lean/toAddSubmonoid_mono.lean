import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable (s : Subsemiring R)

theorem toAddSubmonoid_mono : Monotone (toAddSubmonoid : Subsemiring R → AddSubmonoid R) := Subsemiring.toAddSubmonoid_strictMono.monotone

